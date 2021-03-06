﻿module OpenApiToAstTypesMatchingAndConversion

open System.Collections.Generic
open System.Globalization
open AST
open ASTExt
open FSharp.Compiler.SyntaxTree
open FSharp.Compiler.XmlDoc
open OpenApi

module XmlDoc =

    /// | <{name}>
    /// | {lines}
    /// | </name>
    let tag name lines =
        [ yield "<" + name + ">"
          yield! lines
          yield "</" + name + ">" ]

    /// | <summary>
    /// | {lines}
    /// | </summary>
    let summary lines = tag "summary" lines

    /// | <remarks>
    /// | {lines}
    /// | </remarks>
    let remarks lines = tag "remarks" lines

    /// | <example>
    /// | {lines}
    /// | </example>
    let example lines = tag "example" lines

/// matching OpenAPI string IR to SynType
let strFormatMatch =
    function
    | StringFormat.String
    | PasswordString -> stringType
    | Byte -> arrayOf byteType
    | Binary -> arrayOf byteType
    | DateString -> dateTimeType
    | DateTimeString -> dateTimeOffsetType
    | Custom "uri"
    | Custom "uriref" -> uriType
    | Custom "uuid"
    | Custom "guid"
    | Custom "uid" -> guidType
    | Custom name -> synType name

/// matching OpenAPI primitive type IR to SynType
let primTypeMatch =
    function
    | Any -> objType
    | Int -> intType
    | PrimTypeKind.Long -> int64Type
    | PrimTypeKind.Double -> doubleType
    | Bool -> boolType
    | PrimTypeKind.String strFormat -> strFormatMatch strFormat

/// matching type kinds in responses to create their syntatic types
let rec extractResponseSynType externalName =
    function
    | Prim primType -> primTypeMatch primType
    | Array (innerType, _) -> arrayOf (extractResponseSynType externalName innerType)
    | Option innerType -> optionOf (extractResponseSynType externalName innerType)
    | BuiltIn builtIn -> synType builtIn
    | Object { Name = Some name } -> synType name
    | Object _ when (Option.isSome externalName) -> synType (Option.get externalName)
    | Object anonObject ->
        let fields =
            anonObject.Properties
            |> List.map
            ^ fun (name, typeKind, def) -> AST.ident name, extractResponseSynType (Some name) typeKind

        if fields.IsEmpty then objType else anonRecord fields
    | DU du -> synType du.Name
    | NoType -> unitType

/// Creating AST XML docs from API representation
let xml: Docs option -> PreXmlDoc =
    function
    | None -> PreXmlDoc.Empty
    | Some docs ->
        xmlDocs [ if docs.Summary.IsSome then XmlDoc.summary docs.Summary.Value
                  if docs.Remarks.IsSome then XmlDoc.remarks docs.Remarks.Value
                  if docs.Example.IsSome then XmlDoc.example docs.Example.Value ]

/// Gets own name of the type instead of the name set upwards
let getOwnName kind def =
    match kind with
    | DU du -> Some du.Name
    | Object o -> o.Name
    | _ -> None
    |> Option.defaultWith def

/// extract record definitions from
let extractRecords (schemas: TypeSchema list) =
    // store name and fields of records here
    let recordsDict =
        Dictionary<string, SynField list * Docs option>()
    // store name and cases of records here
    let duDict =
        Dictionary<string, (string * SynType * PreXmlDoc) list * Docs option>()
    
    let rec extractSynType (name: string, kind: TypeKind) =
        match kind with
        | Prim primType -> primTypeMatch primType
        | BuiltIn builtIn -> synType builtIn
        | Array (innerType, _) -> arrayOf (extractSynType (getOwnName innerType (fun () -> name), innerType))
        | Option innerType -> optionOf (extractSynType (getOwnName innerType (fun () -> name), innerType))
        | Object objectKind ->
            let name = getOwnName kind ^ fun _ -> name
            // extract field types
            let fields =
                objectKind.Properties
                |> List.map (fun (fieldName, fieldKind, def) ->
                    extractSynType (fieldName, fieldKind)
                    |> field fieldName)

            // add name and fields for later
            if not ^ recordsDict.ContainsKey name then
                recordsDict.Add(name, (fields, objectKind.Docs))

            // return SynType with record name
            synType name
        | DU du ->
            let cases =
                du.Cases
                |> List.mapi
                   (
                       fun idx case ->
                           let name = case.CaseName |> Option.defaultWith (fun _ -> sprintf "Case%d" (idx + 1))
                           let subtypeName = getOwnName case.Kind (fun _ -> name + "CaseValue")
                           name,
                           extractSynType(subtypeName, case.Kind),
                           xml case.Docs
                   )
            if cases.Length > 0 && not ^ duDict.ContainsKey du.Name then
                duDict.Add(du.Name, (cases, du.Docs))
            synType name
        | NoType -> failwith "Field without types are not supported for record schemas"

    // iterate through schemas
    // records will be stored in dictionary as a side effect
    for schema in schemas do
        extractSynType (schema.Name, schema.Kind)
        |> ignore
    
    // create final DU expressions
    let dus =    
        duDict
        |> Seq.map
        ^ fun (KeyValue(name, (cases, docs))) ->
            discriminatedUnion (xml docs) name cases

    // create final record expressions
    let records =
        recordsDict
        |> Seq.map
        ^ fun (KeyValue (name, (fields, docs))) ->
            let xmlDocs = xml docs
            record xmlDocs name fields
    
    dus
    |> Seq.append records
    |> Seq.toList
    
[<Struct>]
type GeneratedOptionalTypeMappingNameKind =
    | GeneratedType of generatedTypeName:string
    | SourceType of sourceTypeName:string
    
type GeneratedOptionalTypeMapping =
    {
        GeneratedName: string
        Generated: TypeKind
        OriginalName: string
        Original: TypeKind
    }
let mutable private optionalTypes = 0
let rec private generateOptionalTypeInternal kind def nameFromSchema =
    match kind with
    | TypeKind.Object o ->
      let mutable hasPropertiesWithDefault = false
      
      let props =
          o.Properties
          |> List.map ^ fun (name, kind, def) ->
              let (hasDefault, generatedKind), (subGenerated: GeneratedOptionalTypeMapping list) = generateOptionalTypeInternal kind def (Some name)
              if hasDefault then
                  hasPropertiesWithDefault <- true
              let kind = if hasDefault then generatedKind else kind
              subGenerated, (name, kind, def)
      
      let kind =
          {
              o with
                  Name = o.Name
                  |> Option.orElse nameFromSchema
                  |> Option.map (fun x -> x + "ForBinding")
                  |> Option.orElseWith
                         (
                             fun _ ->
                                 sprintf "TemporaryTypeForBinding%d" (System.Threading.Interlocked.Increment(ref optionalTypes)) |> Some
                         )
                  Properties = props |> List.map snd
          }
      let generated =
          [
              if hasPropertiesWithDefault then
                  {
                      OriginalName = o.Name |> Option.orElse nameFromSchema |> Option.get
                      Original = TypeKind.Object o
                      GeneratedName = kind.Name.Value
                      Generated = TypeKind.Object kind
                  }
              yield! props |> Seq.collect fst
          ]
      (hasPropertiesWithDefault, TypeKind.Object kind), generated
    | TypeKind.Option opt ->
        let (hasDef, kind), generated = generateOptionalTypeInternal opt def nameFromSchema
        let kind = if hasDef then kind else opt
        (hasDef, TypeKind.Option kind), generated
    | TypeKind.Array (item, def) ->
        let (hasDef, kind), generated = generateOptionalTypeInternal item def nameFromSchema
        let kind = if hasDef then kind else item
        (hasDef, TypeKind.Array (kind, def)), generated 
    | v ->
      let isDefaultable = Option.isSome def
      let kind = if isDefaultable then TypeKind.Option v else v
      (isDefaultable, kind), []
let generateOptionalType kind def nameFromSchema =
    generateOptionalTypeInternal kind def nameFromSchema
    |> snd

let rec defaultToExpr v =
    let inline cnst syn v =
        constExpr (syn v)
    match v with
    | DefaultableKind.Boolean b -> cnst SynConst.Bool b
    | DefaultableKind.Date d ->
        let components =
            [
              d.Year
              d.Month
              d.Day
            ] |> List.map (cnst SynConst.Int32)
        app (longIdentExpr "System.DateTime") (tupleComplexExpr components)
    | DefaultableKind.Double d -> cnst SynConst.Double d
    | DefaultableKind.Guid g ->
        let gString = g.ToString("D", CultureInfo.InvariantCulture)
        app (longIdentExpr "System.Guid.ParseExact") (tupleComplexExpr [strExpr gString; strExpr "D"])
    | DefaultableKind.Integer i -> cnst SynConst.Int32 i
    | DefaultableKind.Long l -> cnst SynConst.Int64 l
    | DefaultableKind.String s -> strExpr s
    | DefaultableKind.Uri u ->
        let uString = u.ToString()
        app (longIdentExpr "System.Uri") (strExpr uString)
    | DefaultableKind.DateTime dt ->
        let dtTicks = dt.DateTime.Ticks |> DefaultableKind.Long |> defaultToExpr
        let tsTicks = dt.Offset.Ticks |> DefaultableKind.Long |> defaultToExpr
        let ts = app (longIdentExpr "System.TimeSpan.FromTicks") (tupleComplexExpr [ tsTicks ])
        app (longIdentExpr "System.DateTimeOffset") (tupleComplexExpr [ dtTicks; ts ])
    |> paren
    
/// rec module here is for cross-recursion mapping <-> fun x -> mapping
/// mapping -> fun... dependency is required for mapping of options and arrays
/// e.g.
/// Result.map (fun (x: SomeTypeForBinding) ->
///   let v: SomeType =
///     { intWithDefault = x.intWithDefault |> Option.defaultValue 100
///       optionalArrayOfArrayOption =
///         x.optionalArrayOfArrayOption
///         |> Option.map (fun (x: AnotherTypeForBinding array option array) ->
///              x |> Array.map (fun (x: AnotherTypeForBinding array option) ->
///                     x |> Option.map (fun (x: AnotherTypeForBinding array) ->
///                            x |> Array.map (fun (x: AnotherTypeForBinding) ->
///                                   let v: AnotherType =
///                                     { forGodsSakeWhy = x.forGodsSakeWhy |> Option.defaultValue "pa$$word"
///                                       andNonDefaultableToo = x.andNonDefaultableToo}
///                                 )
///                          )
///                   )
///            )
/// )
/// where `fun (x[: Type]) -> [let v = ](mapping);[v]` are generated by generateDefaultMappingFun* family of functions
/// and (mapping) itself is generated by generateDefaultMapping function 
module rec DefaultsGeneration =
    let private generateBestPossibleFunc kind defaultsMap def nameFromSchema =
        getOwnName kind ^ fun _ -> Unchecked.defaultof<string>
        |> Option.ofObj
        |> Option.map GeneratedType
        |> Option.map Map.tryFind
        |> Option.bind ((|>) defaultsMap)
        |> Option.map (generateDefaultMappingFunFromMapping defaultsMap def)
        |> Option.defaultWith (fun _ -> generateDefaultMappingFunFromKind defaultsMap kind def nameFromSchema)
    
    let rec private generateDefaultMapping defaultsMap source def nameFromSchema instanceName =
        let indented = longIdentExpr instanceName
        match source with
            | TypeKind.Object source ->
                let mutable hasDefaultProps = false
                let record =
                    recordExpr
                        [
                            for name, kind, def in source.Properties do
                                let propPath = instanceName + "." + name
                                let hasDefaults, subMapping = generateDefaultMapping defaultsMap kind def name propPath
                                hasDefaultProps <- hasDefaultProps || hasDefaults
                                name, subMapping
                        ]
                if hasDefaultProps then
                    true, record
                else false, indented
            | TypeKind.Array (item, def) ->
                let hasDefaults, func = generateBestPossibleFunc item defaultsMap def nameFromSchema
                if hasDefaults then
                    true, indented ^|> app (longIdentExpr "Array.map") func
                else false, indented
            | TypeKind.Option v ->
                if def.IsSome then
                    true, indented ^|> Option.defaultValueExpr (defaultToExpr def.Value)
                else
                    let hasDefaults, func = generateBestPossibleFunc v defaultsMap def nameFromSchema
                    if hasDefaults then
                        true, indented ^|> Option.mapExpr func
                    else false, indented
            | _ ->
                if def.IsSome then
                    failwith "should be handled by option"
                else
                    false, indented

    let private generateDefaultMappingFunFromKind defaultsMap kind sourceDef nameFromSchema =
        let param = "src"
        let hasDefaults, recordExpr = generateDefaultMapping defaultsMap kind sourceDef nameFromSchema param
        hasDefaults, lambda (simplePats [SynSimplePat.Typed(simplePat param, extractResponseSynType (Some nameFromSchema) kind, r)]) recordExpr

    let private generateDefaultMappingFunFromMapping defaultsMap sourceDef (mapping: GeneratedOptionalTypeMapping) =
        let param = "src"
        let hasDefaults, recordExpr = generateDefaultMapping defaultsMap mapping.Generated sourceDef mapping.OriginalName param
        let bindWithTypeAndReturn =
            letExprComplex (SynPat.Typed(SynPat.Named(SynPat.Wild r, ident "v", false, None, r), synType mapping.OriginalName, r))
                recordExpr (identExpr "v")
        hasDefaults, lambda (simplePats [SynSimplePat.Typed(simplePat param, synType mapping.GeneratedName, r)]) bindWithTypeAndReturn
        
    let generateDefaultMappingFunFromSchema defaultsMap mapping (schema: TypeSchema) =
        let hasDefault, fn = generateDefaultMappingFunFromMapping defaultsMap schema.DefaultValue mapping
        if hasDefault then fn
        else _id