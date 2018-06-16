open System
open System.Collections.Generic
open System.Linq

///////////////////////////////////////////////////////////////////////////////////////
// 以下（メインプログラム行まで）は、推論で使用する辞書を生成するのに必要なコードなので、
// 推論動作に直接関係はありません

// 与えられた型の種別を返すパターン関数
let (|Object|Class|Interface|ValueType|NonApplicable|) (typ: Type) =
    if typ = null then NonApplicable
    elif typ = typeof<System.Object> then Object
    elif typ.IsClass then Class
    elif typ.IsInterface then Interface
    elif typ.IsValueType then ValueType
    else NonApplicable

// 型名を安全に取得する関数
// オープンジェネリック型の場合、FullNameが与えられないため、簡易的な規則で型名を生成する。
let getFullName (typ: Type): string =
    match typ.FullName with
    | null -> typ.Namespace + "." + typ.Name    // 名前空間+型名
    | _ -> typ.FullName

// 型名で比較を行う比較演算子を定義
type TypeComparer() =
    interface IEqualityComparer<Type> with
        member __.Equals(lhs, rhs) = getFullName lhs = getFullName rhs
        member __.GetHashCode(typ) = (getFullName typ).GetHashCode()
    interface IComparer<Type> with
        member __.Compare(lhs, rhs) = (getFullName lhs).CompareTo(getFullName rhs)
let typeComparer = new TypeComparer()

// リストによる差集合演算関数（F#標準関数にないため）: A-B
let inline (-) (a: Type list) (b: Type list): Type list =
    Enumerable.Except(a, b, typeComparer)
    |> Seq.toList
    
// リストによる積集合演算関数（F#標準関数にないため）: A*B
let inline (*) (a: Type list) (b: Type list): Type list =
    Enumerable.Intersect(a, b, typeComparer)
    |> Seq.toList

// リストによる一意化関数
let inline distinct (xs: Type list): Type list =
    Enumerable.Distinct(xs, typeComparer)
    |> Seq.toList

// アブダクション推論のために、代入互換性のある型の探索と収集を行う関数
let crawlAndCollectTypes (tryAdd: Type -> System.Collections.Generic.List<Type> option) (types: Type seq): unit =

    // 指定された型を再帰探索して:
    // 1. 直接的に代入互換のある型を、tryAdd関数で登録する
    // 2. 代入互換性のある型のリストを取得する
    let rec recCrawl (typ: Type): Type list =

        // 代入互換性のある型群を再帰探索して処理する
        let recCrawlCompatibleTypes (compatibleTypes: Type list): Type list =
            // プレースホルダとしてミュータブルなリストを登録する
            match tryAdd typ with
            // この型の処理が初回なら
            | Some(placeholder) ->
                // 基底型とインターフェイス型群を再帰探索し、探索した型に代入互換性のあった全ての型を取得
                let compatibleBaseTypes =
                    compatibleTypes
                    |> List.collect recCrawl
                    |> distinct

                // この型の代入互換型から除外することで、直接的に代入互換のある型のみに絞って返す。
                // 本来不要だが、逐次的に推論が行われることを確認するため: (A)
                // int[]型について得られる情報:
                //   System.Int32[]:    // 以下以外の型もあるが省略
                //     System.Int32[] -> System.IList
                //     System.Int32[] -> System.ICollection
                //     System.Int32[] -> System.IEnumerable
                //   System.IList:
                //     System.IList -> System.ICollection
                //     System.IList -> System.IEnumerable
                //   System.ICollection:
                //     System.ICollection -> System.IEnumerable
                // 直接的に代入互換のある型に絞ったリストを辞書に加える:
                //   System.Int32[]:
                //     System.Int32[] -> System.IList
                //   System.IList:
                //     System.IList -> System.ICollection
                //   System.ICollection:
                //     System.ICollection -> System.IEnumerable
                // 上記のように制限すれば、
                //   1) System.Int32[] -> System.IList
                //   2) System.IList -> System.ICollection
                //   3) System.ICollection -> System.IEnumerable
                // のような推論のための情報を準備できる。
                let relatedTypes =
                    compatibleTypes - compatibleBaseTypes

                // 直接的に代入互換のある型をプレースホルダに追加する
                relatedTypes |> List.iter(placeholder.Add)

                // 代入互換性のある全ての型を返す（再帰で使用する）
                compatibleTypes
            
            // この型は処理済み、又は処理中（の再帰探索中）
            | None ->
                // 代入互換性のある全ての型を返す（再帰で使用する）
                compatibleTypes

        match typ with
        // obj型は他の型への代入互換性はない（obj自身へのみ可能）
        | Object ->
            // obj型のみ登録する
            tryAdd typ |> ignore

            // 代入互換性のある型はない
            []

        // クラス型・値型は、基底型とインターフェイス型を再帰探索する
        | Class
        | ValueType ->
            // この型に代入互換性のある、基底型とインターフェイス型群を取得して処理する
            let compatibleTypes = typ.BaseType :: (typ.GetInterfaces() |> List.ofArray)
            recCrawlCompatibleTypes compatibleTypes

        // インターフェイス型は、インターフェイス型を再帰探索する
        | Interface ->
            // この型に代入互換性のある、インターフェイス型群を取得して処理する
            let compatibleTypes = typ.GetInterfaces() |> List.ofArray
            recCrawlCompatibleTypes compatibleTypes

        // 上記以外の型は今回取り扱わない
        | NonApplicable ->
            []

    // 型の集合全体を再帰探索する
    types |> Seq.iter(fun typ -> recCrawl typ |> ignore)


// アブダクション推論のための辞書引きを行う関数を生成する。
// 関数は、「代入する型」を与えると、「直接代入互換性のある型」のリストが得られる。
let createDictionaryAccessor(): Type -> Type list =

    // 調べた型を辞書に追加する関数
    // 初めてこの型が追加された場合、直接代入互換性のある型群を格納するためのリストを返す。
    let results = new Dictionary<Type, System.Collections.Generic.List<Type>>(typeComparer)
    let tryAdd (typ: Type): System.Collections.Generic.List<Type> option =
        match results.TryGetValue(typ) with
        | (true, _) -> None
        | _ ->
            let placeholder = new System.Collections.Generic.List<Type>()
            results.Add(typ, placeholder)
            Some(placeholder)
            
    // 空のリスト
    let emptyList = new System.Collections.Generic.List<Type>()

    // 任意の型を指定すると、直接代入互換性がある型のリストを返す関数を定義する
    let accessor (typ: Type): Type list =
        // 辞書への追加を試みる
        crawlAndCollectTypes tryAdd [typ]
        // 辞書から結果を取得する
        results.GetValueOrDefault(typ, emptyList) |> Seq.toList

    // コアライブラリ全体を予め辞書に登録する
    // 事前にすべての型を辞書に入れておけば、推論速度が向上する（キャッシング）。
    // ただし、キャッシュを行わず、要求に応じてオンデマンドで探索しても結果は変わらない。
    //typeof<System.Object>.Assembly.GetTypes()
    //    |> Seq.iter(fun typ -> accessor typ |> ignore)

    // アクセサ関数を返す
    accessor
    
///////////////////////////////////////////////////////////////////////////////////////
// メインプログラム

// テスト用に、型の集合を安全に比較できる関数を定義する
let typesEquals (a: Type list) (b: Type list): bool =
    // 両方のリストを型名でソートし、一致するかどうかを返す
    let orderedA = Enumerable.OrderBy(a, (fun typ -> typ), typeComparer)
    let orderedB = Enumerable.OrderBy(b, (fun typ -> typ), typeComparer)
    orderedA.SequenceEqual(orderedB, typeComparer)

// このコードは総称型に対応していないため、総称型をフィルタする関数を定義しておく
let isNonGenericTypes (typ: Type): bool =
    not (typ.IsGenericType || typ.IsGenericTypeDefinition)
let filterGenericTypes (types: Type list): Type list =
    types |> List.filter isNonGenericTypes

// ---------------------------------

// アブダクション推論を実行する
let abduction (origins: Type list) (accessor: Type -> Type list): Type list =

    // アブダクション辞書を再帰的に探索する関数
    let rec recAbduction (typ: Type): Type list =

        // 1. 型に対応する代入互換性のある型群を、アクセサ関数を使って取得する
        // （見つからない場合は空のリストが返される）
        let compatibleTypes = accessor typ

        // 推論経過をダンプします
        if isNonGenericTypes typ then
            printfn "%A: %A" typ (compatibleTypes |> filterGenericTypes)

        // 2. これらの型について再帰的に探索する
        // int[] -> [ Array ], Array -> [ IList ], ... のように探索することになる
        let collectedTypes = compatibleTypes |> List.collect recAbduction

        // 3. 得られた型のリストを、全て結合する
        // 同じ型を列挙する可能性があるので、一意化する
        compatibleTypes
            |> List.append collectedTypes
            |> distinct

    // 与えられた型群の探索を行う
    // 与えられた型同士は、お互いに代入互換性があることを積集合で計算できる:
    //   int[]:  Array, obj, IList, ICollection, IEnumerable, ICloneable, ...
    //   string: obj, IConvertible, IFormattable, IEnumerable, ICloneable, ...
    // 上記の積集合で、obj, IEnumerable と ICloneable が抽出される。
    origins
        |> List.map (recAbduction >> filterGenericTypes)    // （総称型はここで除外しておく）
        |> List.reduce (*)

// ---------------------------------

open System.Diagnostics

// テスト1: 指定された型のアブダクション推論(1回)が成功する
let abductionOnceTest (accessor: Type -> Type list): unit =

    // アクセサ関数を使って、手動で推論を実行する。
    // 例: 配列 (int[]) は、列挙可能型 (IEnumerable) を実装しているが、これを推論するには階層構造をたどる必要がある:
    //     int[] -> Array             -- 1)
    //     Array -> IList             -- 2)
    //     IList -> ICollection       -- 3)
    //     ICollection -> IEnumerable -- 4)
    // 以下のコード片は、これを手動で実行する。

    // 1) int[] -> [ Array ]
    let intArrayCompatibleTypes =
        accessor typeof<int[]>
        |> filterGenericTypes   // （不完全な総称型が含まれるため、結果をフィルタする）
    Debug.Assert(typesEquals intArrayCompatibleTypes [ typeof<Array> ])

    // 2) Array -> [ obj, IList, ... ]
    let arrayCompatibleTypes =
        accessor typeof<Array>
        |> filterGenericTypes
    Debug.Assert(typesEquals arrayCompatibleTypes
        [ typeof<obj>;
        typeof<System.Collections.IList>;
        typeof<System.ICloneable>;
        typeof<System.Collections.IStructuralComparable>;
        typeof<System.Collections.IStructuralEquatable>] )

    // 3) IList -> [ ICollection ]
    let listCompatibleTypes =
        accessor typeof<System.Collections.IList>
        |> filterGenericTypes
    Debug.Assert(typesEquals listCompatibleTypes
        [ typeof<System.Collections.ICollection> ] )

    // 4) ICollection -> [ IEnumerable ]
    let collectionCompatibleTypes =
        accessor typeof<System.Collections.ICollection>
        |> filterGenericTypes
    Debug.Assert(typesEquals collectionCompatibleTypes
        [ typeof<System.Collections.IEnumerable> ] )    // IEnumerableが推論された

// ---------------------------------

// テスト2: 指定された型のアブダクション推論を、推論可能な全ての型について実行する
let recursiveAbductionTest (accessor: Type -> Type list): unit =
    
    // a) 代入互換性を網羅する辞書
    // b) 型のリスト
    // を与えることで、b)全てに代入互換性のある型を推論する。

    // 以下のように int[] と string が与えられた場合、両方に互換性のある型は、
    // obj, IEnumerable と ICloneable になる。

    let origins = [ typeof<int[]>; typeof<string> ]

    let results = abduction origins accessor
    Debug.Assert(typesEquals results
        [ typeof<obj>;
        typeof<System.Collections.IEnumerable>;
        typeof<System.ICloneable>] )
    
// ---------------------------------

[<EntryPoint>]
let main argv =
    // アブダクションで使用する辞書へのアクセサ関数を取得する

    // このアクセサ関数は代入互換性を調べる事ができて、「代入する型」->「代入される型」を導出する:
    // インターフェイス型はランタイムの定義上、階層構造を持っていないが、この辞書では階層構造を
    // 模している (A)
    let accessor: Type -> Type list = createDictionaryAccessor()

    // アクセサ関数を使って、テストを実行する

    // テスト1
    abductionOnceTest accessor

    // テスト2
    recursiveAbductionTest accessor

    0
