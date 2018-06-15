open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.Linq

///////////////////////////////////////////////////////////////////////////////////////
// 以下は推論で使用する辞書を生成するのに必要なコードなので、推論動作には関係ありません

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
let typeComparer = { new IEqualityComparer<Type> with
    member __.Equals(lhs, rhs) = getFullName lhs = getFullName rhs
    member __.GetHashCode(typ) = (getFullName typ).GetHashCode() }

// リストによる差集合演算関数（F#標準関数にないため）: A-B
let inline (-) (a: Type list) (b: Type list): Type list =
    Enumerable.Except(a, b, typeComparer)
    |> Seq.toList

// リストによる一意化関数
let inline distinct (xs: Type list): Type list =
    Enumerable.Distinct(xs, typeComparer)
    |> Seq.toList

// 空のリスト
let emptyList = new System.Collections.Generic.List<Type>()

// アブダクション推論のための辞書を作成する。
// 辞書は、「代入する型」を与えると、「代入される型」のリストが得られる。
let crawlAndCollectTypes (tryAdd: Type -> System.Collections.Generic.List<Type> -> unit) (types: Type seq): unit =

    // 指定された型を再帰探索して:
    // 1. 直接的に代入互換のある型を、tryAdd関数で登録する
    // 2. 代入互換性のある型のリストを取得する
    let rec recCrawl (typ: Type): Type list =
        match typ with
        // obj型は他の型への代入互換性はない
        |Object ->
            // 空のリストを登録する
            let placeholder = new System.Collections.Generic.List<Type>()
            tryAdd typ placeholder

            // 代入互換性のある型はない
            []

        // クラス型・値型は、基底型とインターフェイス型を再帰探索する
        |Class
        |ValueType ->
            // プレースホルダとしてミュータブルなリストを登録しておき、中身は後で更新する
            let placeholder = new System.Collections.Generic.List<Type>()
            tryAdd typ placeholder

            // 基底型とインターフェイス型群を再帰探索し、探索した型に代入互換性のあった全ての型を取得
            let compatibleTypes = typ.BaseType :: (typ.GetInterfaces() |> List.ofArray)
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
            relatedTypes
                // （今回は総称型は除外する）
                |> List.filter(fun typ -> not typ.IsGenericType && not typ.IsGenericTypeDefinition)
                |> List.iter(placeholder.Add)

            // 代入互換性のある全ての型を返す（再帰で使用する）
            compatibleTypes

        // インターフェイス型は、インターフェイス型を再帰探索する
        |Interface ->
            // プレースホルダとしてミュータブルなリストを登録しておき、中身は後で更新する
            let placeholder = new System.Collections.Generic.List<Type>()
            tryAdd typ placeholder

            // インターフェイス型群を再帰探索し、探索した型に代入互換性のあった全ての型を取得
            let compatibleTypes = typ.GetInterfaces() |> List.ofArray
            let compatibleBaseTypes =
                compatibleTypes
                |> List.collect recCrawl
                |> distinct

            // この型の代入互換型から除外することで、直接的に代入互換のある型のみに絞って返す。
            let relatedTypes =
                compatibleTypes - compatibleBaseTypes

            // 直接的に代入互換のある型をプレースホルダに追加する
            relatedTypes
                // （今回は総称型は除外する）
                |> List.filter(fun typ -> not typ.IsGenericType && not typ.IsGenericTypeDefinition)
                |> List.iter(placeholder.Add)

            // 代入互換性のある全ての型を返す（再帰で使用する）
            compatibleTypes

        // 上記以外の型は今回取り扱わない
        |NonApplicable ->
            []

    // 型の集合全体を再帰探索する
    types |> Seq.iter(fun typ -> recCrawl typ |> ignore)


// アブダクション推論のための辞書引きを行う関数を、コアライブラリ全体から作成する。
let createDictionaryAccessorFromCoreLibrary(): Type -> Type list =

    // 辞書に追加する関数の定義（重複を除去する）
    let results = new ConcurrentDictionary<Type, System.Collections.Generic.List<Type>>()
    let tryAdd typ relatedTypes =
        results.TryAdd(typ, relatedTypes) |> ignore

    // コアライブラリの型全体に上記の関数を適用して、辞書を一旦完成させる
    let coreLibrary = typeof<System.Object>.Assembly
    coreLibrary.GetTypes() |> crawlAndCollectTypes tryAdd

    // この後アドホック的に使える関数を返す
    fun typ ->
        // 辞書への追加を試みる
        crawlAndCollectTypes tryAdd [typ]
        // 辞書から結果を取得する
        results.GetValueOrDefault(typ, emptyList) |> Seq.toList
    
///////////////////////////////////////////////////////////////////////////////////////
// メインプログラム

// アブダクション推論を実行する
let abduction (origins: Type list) (accessor: Type -> Type list): Type list =

    // アブダクション辞書を再帰的に探索する関数
    let rec recAbduction (currents: Type list): Type list =
        // 与えられた型（すべて）について、以下の集合を全て集約する:
        currents
            |> List.collect(fun typ ->
                // 型に対応する代入互換性のある型群を取得する
                // （見つからない場合は空のリストが返される）
                let compatibleTypes = accessor typ
                // これらの型について再帰的に探索する
                recAbduction compatibleTypes)
            |> distinct

    // 与えられた型群の探索を行う
    recAbduction origins

[<EntryPoint>]
let main argv =
    // アブダクションで使用する辞書へのアクセサを取得する

    // この辞書は代入互換性を調べる事ができて、「代入する型」->「代入される型」を導出する:
    // インターフェイス型はランタイムの定義上、階層構造を持っていないが、この辞書では階層構造を
    // 模している (A)

    // 例: 配列 (int[]) は、列挙可能型 (IEnumerable) を実装しているが、階層構造を
    //     たどる必要がある: int[] -> IList, IList -> ICollection, ICollection -> IEnumerable
    let accessor: Type -> Type list = createDictionaryAccessorFromCoreLibrary()

    let intArrayCompatibleTypes = accessor typeof<int[]>

    // a) 代入互換性を網羅する辞書
    // b) 型のリスト
    // を与えることで、b)全てに代入互換性のある型を推論する。

    // 以下のように int[] と string が与えられた場合、両方に互換性のある型は、
    // ICloneable と IEnumerable になる。

    let origins = [ typeof<int[]>; typeof<string> ]

    let results = abduction origins accessor
    
    printfn "origins = %A" origins
    printfn "results = %A" results

    0
