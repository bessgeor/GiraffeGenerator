module CodeGenNullChecking

open AST
open ASTSeqBuilder
open ASTExt
open FSharp.Compiler.SyntaxTree
open OpenApi
open OpenApiToAstTypesMatchingAndConversion

type private PropertyPathSegment =
  | Property of string
  | NullableValue
  | CollectionValue of PropertyPathSegment
  | OptionValue of PropertyPathSegment

let private isNullReference = "isNullReference"
let private nullReferenceToOption = "nullReferenceToOption"
let private checkForUnexpectedNullsName = "checkForUnexpectedNulls"
let generateNullCheckingHelpers () =
    [
        // isNullReference
        letDecl false isNullReference ["v"] None // (=) doesn't work because F# thinks that C# can't fuck it up on nulls
            ^ app (longIdentExpr "System.Object.ReferenceEquals")
                (tupleComplexExpr [ identExpr "v"; SynExpr.Null(r) ])
        // nullReferenceToOption
        letDecl false nullReferenceToOption ["v"] None
            ^ ifElseExpr (app (identExpr isNullReference) (identExpr "v"))
                (identExpr "None")
                (app (identExpr "Some") (identExpr "v"))
        // checkForUnexpectedNulls
        let checkForUnexpectedNulls =
            let checkers = "checkers"
            let errType = "errType"
            let value = "value"
            let mapChecked = "mapChecked"
            letDecl false checkForUnexpectedNullsName [checkers; errType; value] None
            ^ letExpr mapChecked ["path"]
                (
                    app (identExpr CodeGenErrorsDU.errInnerModelBindingUnexpectedNull)
                        (
                            recordExpr
                                [
                                    "PropertyPath", identExpr "path"
                                ]
                        )
                )
                (
                    app (identExpr checkers) (identExpr value)
                    ^|> Seq.mapExpr (identExpr mapChecked)
                    ^|> longIdentExpr "Seq.toArray"
                    ^|> lambda (simplePats[simplePat "v"])
                        (
                            ifElseExpr (app (appI (identExpr "op_Equals") (longIdentExpr "v.Length")) (constExpr (SynConst.Int32 0)))
                                (app (identExpr "Ok") (identExpr value))
                                (
                                    ifElseExpr
                                        (app (appI (identExpr "op_GreaterThan") (longIdentExpr "v.Length")) (constExpr (SynConst.Int32 1)))
                                        (identExpr "v" ^|> identExpr CodeGenErrorsDU.errInnerCombined)
                                        (identExpr "v" ^|> longIdentExpr "Array.head")
                                    ^|> identExpr errType
                                    ^|> identExpr "Error"
                                )
                        )
                )
        checkForUnexpectedNulls
    ]

let checkIsNR = identExpr isNullReference

let private mayPrimitiveBindToNull =
    function
    | PrimTypeKind.Any -> true
    | PrimTypeKind.String s ->
        match s with
        | StringFormat.DateString
        | StringFormat.DateTimeString
        | StringFormat.Custom _ -> false
        | _ -> true
    | _ -> false

let rec kindHasNullableValues =
    function
    | TypeKind.Array _
    | TypeKind.Object _
    | TypeKind.DU _ -> true
    | TypeKind.BuiltIn _
    | TypeKind.NoType -> false
    | TypeKind.Option o -> kindHasNullableValues o 
    | TypeKind.Prim prim -> mayPrimitiveBindToNull prim

// rec is for cross-recursion
module private rec NullCheckGeneration =
    let noop = yieldFromExpr (longIdentExpr "Seq.empty")
    
    let private generateLambda pats currentPath lastIndex kind originalName =
        let pats1 = simplePats pats |> Some |> Option.filter (fun _ -> pats.Length > 0)
        let pats2 = 
            [
                yield SynSimplePat.Typed(simplePat "x", extractResponseSynType originalName kind, r)
            ] |> simplePats
            
        let r =
            generateNullAccessesFromType currentPath lastIndex "x" kind originalName
            |> Option.map (fun body -> seqCEExpr body |> paren)
            |> Option.map (lambda pats2)
        r
        |> Option.map2 lambda pats1
        |> Option.orElse r
        
    let private generateIndexName = sprintf "i%d"
    
    let private generatePathExpr path lastIndex =
        if lastIndex = 0 then strExpr path
        else
            let indices =
                [1..lastIndex]
                |> List.map generateIndexName
                |> List.map identExpr
            let sprintfCall = sprintfExpr path indices |> paren
            sprintfCall

    let private yieldNRIfNullOr currentPath lastIndex expr =
        let check = app checkIsNR (longIdentExpr expr)
        let yieldNR = generatePathExpr currentPath lastIndex
        ifElseExpr check yieldNR
        
    let private generateArrayMapLambda currentPath lastIndex kind originalName =
        let currentPath = currentPath + ".[%d]"
        let lastIndex = lastIndex + 1
        let pats = [simplePat ^ generateIndexName lastIndex] 
        generateLambda pats currentPath lastIndex kind originalName
        
    let private generateArrayMapping currentPath lastIndex expr kind originalName =
        let lambda = generateArrayMapLambda currentPath lastIndex kind originalName
        let iterateArray =
            lambda
            |> Option.map (fun lambda ->
                longIdentExpr expr
                ^|> Seq.mapiExpr lambda
                ^|> Seq.collectExpr _id
                |> yieldFromExpr)
            |> Option.defaultValue noop
        yieldNRIfNullOr currentPath lastIndex expr iterateArray
        
    let private generateOptionMapLambda currentPath lastIndex kind originalName =
        let currentPath = currentPath + "?.Value" 
        generateLambda [] currentPath lastIndex kind originalName
        
    let private generateOptionMapping currentPath lastIndex expr kind originalName =
        generateOptionMapLambda currentPath lastIndex kind originalName
        |> Option.map (fun lambda ->
            longIdentExpr expr
            ^|> Option.mapExpr lambda
            ^|> Option.defaultValueExpr (longIdentExpr "Seq.empty")
            |> yieldFromExpr
        )
        
    let private generateObjectPropertyMapping currentPath lastIndex expr property =
        let (name, kind, _) = property
        let expr = expr + "." + name 
        let currentPath = currentPath + "." + name
        generateNullAccessesFromType currentPath lastIndex expr kind (Some name)
        
    let private generateObjectMapping currentPath lastIndex expr (obj: ObjectKind) =
        let props =
            obj.Properties
            |> Seq.map (generateObjectPropertyMapping currentPath lastIndex expr)
            |> Seq.choose id
            |> Seq.toList
        let iterateProps =
            Some props
            |> Option.filter (List.tryHead >> Option.isSome)
            |> Option.map seqCEExprList
            |> Option.defaultValue noop
        yieldNRIfNullOr currentPath lastIndex expr iterateProps
        
    let private generateNullAccessesFromType currentPath lastIndex expr kind originalName =
        match kind with
        | TypeKind.Array (item, _) ->
            generateArrayMapping currentPath lastIndex expr item originalName |> Some
        | TypeKind.Option item ->
            generateOptionMapping currentPath lastIndex expr item originalName
        | TypeKind.Object obj ->
            generateObjectMapping currentPath lastIndex expr obj |> Some
        | TypeKind.Prim prim ->
            let isNullable = mayPrimitiveBindToNull prim
            if isNullable then
                yieldNRIfNullOr currentPath lastIndex expr noop |> Some
            else None
        | TypeKind.BuiltIn _
        | TypeKind.DU _
        | TypeKind.NoType -> failwithf "Null-checking is not supported for kind %A" kind
            
        
    let generateNullAccessLambda varName (schema: TypeSchema) =
        generateLambda [] varName 0 schema.Kind (Some schema.Name)

let x = {| a = {| aa = "" |}; b = ""; c = Some [| [| Some [| Some {| cc = "" |} |] |] |] |}
let isNR x = true
let xx =
    let nrs =
        seq {
            if isNR x then "x"
            else
                if isNR x.a then "x.a"
                else
                    if isNR x.a.aa then "x.a.aa"
                if isNR x.b then "x.b"
                yield!
                    x.c
                    |> Option.map (fun a ->
                            seq {
                                if isNR a then "x.c?.Value"
                                else
                                    yield!
                                        a
                                        |> Seq.mapi (fun i1 a ->
                                            seq {
                                                if isNR a then (sprintf "x.c?.Value.[%d]" i1)
                                                else
                                                    yield!
                                                        a
                                                        |> Seq.mapi (fun i2 a ->
                                                            seq {
                                                                if isNR a then (sprintf "x.c?.Value.[%d].[%d]" i1 i2)
                                                                else
                                                                    let op =
                                                                        a
                                                                        |> Option.map (fun a ->
                                                                                seq {
                                                                                    if isNR a then (sprintf "x.c?.Value.[%d].[%d]?.Value" i1 i2)
                                                                                    else
                                                                                        yield!
                                                                                            a
                                                                                            |> Seq.mapi (fun i3 a ->
                                                                                                    seq {
                                                                                                        if isNR a then (sprintf "x.c?.Value.[%d].[%d]?.Value.[%d]" i1 i2 i3)
                                                                                                        else
                                                                                                            let op =
                                                                                                                a
                                                                                                                |> Option.map (fun a ->
                                                                                                                    seq {
                                                                                                                        if isNR a then (sprintf "x.c?.Value.[%d].[%d]?.Value.[%d]?.Value" i1 i2 i3)
                                                                                                                        else
                                                                                                                            if isNR a.cc then (sprintf "x.c?.Value.[%d].[%d]?.Value.[%d]?.Value.cc" i1 i2 i3)
                                                                                                                    })
                                                                                                            if a.IsSome then yield! op.Value
                                                                                                    }
                                                                                                ) |> Seq.collect id
                                                                                }
                                                                            )
                                                                    if op.IsSome then yield! op.Value
                                                            }) |> Seq.collect id
                                            }) |> Seq.collect id
                                    
                            }
                        )
                    |> Option.defaultValue Seq.empty
        }
    let nrs =
        nrs
        |> Seq.toArray
    if nrs.Length = 0 then None
    else Some nrs


let bindNullCheckIntoResult varName schema error expr =
    let nullChecker = NullCheckGeneration.generateNullAccessLambda varName schema
    nullChecker
    |> Option.map ^ fun checker ->
        expr
        ^|> Result.bindExpr
        ^ paren
            (
                app (app (identExpr checkForUnexpectedNullsName) checker)
                    (identExpr error)
            ) 
    |> Option.defaultValue expr
