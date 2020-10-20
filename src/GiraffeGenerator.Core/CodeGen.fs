module CodeGen

open System.Globalization
open AST
open ASTExt
open OpenApi
open OpenApiToAstTypesMatchingAndConversion
open Fantomas
open FSharp.Compiler.SyntaxTree

/// helper function to create partial Giraffe flow:
/// {method.Method} >=> service.{method.Name}
let createMethod (method: PathMethodCall) =
    method.Method.ToUpperInvariant()
    |> identExpr
    >=> service method.Name

let private createRouteHandler path method =
    let verb =
        method.Method.ToUpperInvariant() |> identExpr

    let serviceCall = service method.Name
    let hasPathParameters =
        method.Parameters
        |> Option.map (Map.containsKey Path)
        |> Option.defaultValue false
    if hasPathParameters then verb >=> routeBind path serviceCall else verb >=> route path >=> serviceCall

/// helper function to create Giraffe flows:
/// {method.Method} >=> route {path.Route} >=> service.{method.Name}
/// or
/// {method.Method} >=> routeBind {path.Route} service.{method1.Name}
/// or
/// choose [
///     {method1.Method} >=> route {path.Route} >=> service.{method.Name}
///     {method2.Method} >=> routeBind {path.Route} service.{method1.Name}
/// ]
let createRoute (path: ParsedPath) =
    if path.Methods.Length > 1 then
        chooseExpr
            (path.Methods
             |> List.map (createRouteHandler path.Route))
    else
        let routeExpr = createRouteHandler path.Route (path.Methods.[0])
        // Without explicit parenthesizing two bad things happen:
        // 1. `>=>` ignores SynExpr.App isInfix flag and generates prefix application for some obscure reason
        // 2. application is ambiguous because the lack of parenthesis
        // e.g. generated code is
        // >=> POST bindRoute "route/{args}" service.Post next ctx
        // instead of
        // (POST >=> bindRoute "route/{args}" service.Post) next ctx
        // or at least
        // ((>=>) POST (bindRoute "route/{args}" service.Post) next ctx
        paren routeExpr

let requestCommonInputTypeName (method: PathMethodCall) = method.Name + method.Method + "Input"
let sourceSorting (source: PayloadLocation) = source = Path, source = Query, source = Body(Json), source = Body(Form)
let isBody = function | Body _ -> true | _ -> false
let isNotBody = isBody >> not

let extractParameterObjectNamesWithLocations (parameterLocation, (parameterSchema: TypeSchema)) =
    let names =
        match parameterSchema.Kind with
        | TypeKind.Object obj -> obj.Properties |> Seq.map (fun (nm,_,_) -> nm)
        | _ -> seq { parameterSchema.Name }
    names |> Seq.map (fun name -> name, parameterLocation)

let getUniqueParameterNameForLocationOrFail ((parameterName, parameterLocations): string * (PayloadLocation[])) =
    if parameterLocations.Length = 1 then
        seq { parameterName, (parameterLocations.[0], parameterName) }
    else
        let hasUnnameable =
            parameterLocations.Length <> (Set parameterLocations).Count
        if hasUnnameable then
            failwithf "Unable to generate distinct input property name: property \"%s\" is duplicated by location" parameterName
        parameterLocations |> Seq.map (fun loc -> parameterName + "From" + (loc.ToString()), (loc, parameterName))

type CombinedRecordPropertyNamesMapping =
    { CombinedRecordPropertyName: string
      OriginalLocation: PayloadLocation
      OriginalName: string }
let getCombinedRecordPropertyNamesFrom parameters =
    parameters
    |> Map.toSeq
    |> Seq.filter (fst >> isNotBody)
    |> Seq.collect extractParameterObjectNamesWithLocations
    |> Seq.groupBy fst
    |> Seq.map (fun (parameterName, group) -> parameterName, group |> Seq.map (fun (_, parameterLocation) -> parameterLocation) |> Seq.toArray)
    |> Seq.collect getUniqueParameterNameForLocationOrFail
    |> Seq.groupBy fst
    // implicit failwith just in case getUniqueParameterNameForLocation fail to do it's job
    |> Seq.map (fun (combinedTypePropertyName, v) -> combinedTypePropertyName, v |> Seq.map snd |> Seq.exactlyOne)
    |> Seq.map (fun (combinedPropertyName, (originalLocation, originalName)) ->
        {
            CombinedRecordPropertyName = combinedPropertyName
            OriginalLocation = originalLocation
            OriginalName = originalName
        })
let generateCombinedRecordTypeDefnFor parameters name =
    let mapping =
        getCombinedRecordPropertyNamesFrom parameters
        |> Seq.map ^ fun mapping -> mapping.OriginalLocation, (mapping.OriginalName, mapping.CombinedRecordPropertyName)
        |> Seq.groupBy fst
        |> Seq.map (fun (k, v) -> k, v |> Seq.map snd |> Map)
        |> Map
    { // generate combined input record from every source of input 
        Name = name
        DefaultValue = None
        Docs = None
        Kind =
            {
                Name = Some name
                Docs = None
                Properties =
                    parameters
                    |> Map.toSeq
                    |> Seq.filter (fst >> isNotBody)
                    |> Seq.collect
                        (
                            fun (location, schema) ->
                                let mapping = mapping |> Map.find location
                                match schema.Kind with
                                | Object o ->
                                    [for name, kind, def in o.Properties do
                                        mapping |> Map.find name, kind, def]
                                | _ -> [mapping |> Map.find (getOwnName schema.Kind ^ fun () -> schema.Name), schema.Kind, schema.DefaultValue]
                        )
                    |> Seq.toList
            } |> TypeKind.Object
    } 
    
let hasMultipleNonBodyParameters parameters =
    parameters
    |> Map.toSeq
    |> Seq.map fst
    |> Seq.filter isNotBody
    |> Seq.length > 1

/// Creating whole module AST for Giraffe webapp
let giraffeAst (api: Api) =
    moduleDecl
        (xml api.Docs)
        api.Name
        [ openDecl "FSharp.Control.Tasks.V2.ContextInsensitive"
          openDecl "Giraffe"
          openDecl "System.Threading.Tasks"
          openDecl "Microsoft.AspNetCore.Http"
          
          let tmpBindingSchemas =
              [ for path in api.Paths do
                  for method in path.Methods do
                      if method.Parameters.IsSome then
                        for KeyValue(source, schema) in method.Parameters.Value do
                            if source = Query || isBody source then // non-query and non-body bindings don't support default values
                                let generatedTypes = generateOptionalType schema.Kind schema.DefaultValue (Some schema.Name)
                                yield! generatedTypes ]
          let tmpBindingSchemasMap =
              tmpBindingSchemas
              |> Seq.collect (fun v -> [ SourceType v.OriginalName, v; GeneratedType v.GeneratedName, v ])
              |> Map

          let allSchemas =
              [
                yield! CodeGenErrorsDU.typeSchemas
                yield! api.Schemas
                yield! tmpBindingSchemas |> Seq.map ^ fun v -> { Kind = v.Generated; Name = v.GeneratedName; Docs = None; DefaultValue = None }
                for path in api.Paths do
                  for method in path.Methods do
                      if method.Parameters.IsSome then
                        for KeyValue(_, schema) in method.Parameters.Value do
                            schema
                        if hasMultipleNonBodyParameters method.Parameters.Value then
                            let name = requestCommonInputTypeName method
                            generateCombinedRecordTypeDefnFor method.Parameters.Value name]

          if not allSchemas.IsEmpty then
              yield! [
                 types (extractRecords allSchemas)

                 // generate helper functions for error handling
                 yield! CodeGenErrorsDU.generateHelperFunctions()

                 // generate helper functions for null checking
                 yield! CodeGenNullChecking.generateNullCheckingHelpers()
              ]

          abstractClassDecl
              "Service"
              [ for path in api.Paths do
                  for method in path.Methods do
                      let responseTypes =
                          [ for response in method.Responses do
                              extractResponseSynType None response.Kind ]
                      
                      // multiple non-body input sources should be combined
                      let combinedTypeName = requestCommonInputTypeName method
                      let maybeCombinedTypeOpenApi =
                          allSchemas |> List.tryFind (fun x -> x.Name = combinedTypeName)  
                      let maybeCombinedType =
                          maybeCombinedTypeOpenApi
                          |> Option.map (fun tp -> tp.Kind |> extractResponseSynType (Some tp.Name))
                          
                      // ...but there may be only one non-body source for which there's no point in generating "combined" type
                      let maybeSingleNonBodyParameterOpenApi =
                          method.Parameters
                          |> Option.bind (fun p -> p |> Map.toSeq |> Seq.filter (fst >> isNotBody) |> Seq.tryExactlyOne)
                      let maybeSingleNonBodyParameter =
                          maybeSingleNonBodyParameterOpenApi
                          |> Option.map snd
                          |> Option.map (fun x -> x.Kind |> extractResponseSynType (Some x.Name))
                          
                      // ...and body should be passed as a separate parameter. TODO: Body binding into DU case per content-type
                      let maybeBodyOpenApi =
                          method.Parameters
                          |> Option.bind (fun p -> p |> Map.toSeq |> Seq.filter (fst >> isBody) |> Seq.tryExactlyOne)
                      let maybeBody =
                          maybeBodyOpenApi
                          |> Option.map snd
                          |> Option.map (fun x -> x.Kind |> extractResponseSynType (Some x.Name))
                          
                      let maybePathOpenApi =
                          method.Parameters
                          |> Option.bind ^ fun p ->
                              p
                              |> Map.toSeq
                              |> Seq.filter (fst >> ((=) Path))
                              |> Seq.map snd
                              |> Seq.tryExactlyOne
                      let maybePath = maybePathOpenApi |> Option.map (fun x -> x.Kind |> extractResponseSynType (Some x.Name))
                          
                      let maybeNonBody = maybeCombinedType |> Option.orElse maybeSingleNonBodyParameter
                          
                      let maybeParams =
                          maybeBody
                          |> Option.map2 (fun a b -> [a; b]) maybeNonBody
                          |> Option.map tuple
                          |> Option.orElse maybeBody
                          |> Option.orElse maybeNonBody

                      // emitting httpHandler abstract method or property
                      maybePath
                      |> Option.map ^ fun pathParam ->
                             // <summary>{method.Docs}</summary>
                             // abstract {method.Name}: {pathParam} -> HttpHandler  
                             abstractMemberDfn (xml method.Docs) method.Name (pathParam ^-> synType "HttpHandler")
                      |> Option.defaultWith ^ fun _ ->
                             // <summary>{method.Docs}</summary>
                             // abstract {method.Name}: HttpHandler
                             abstractGetterDfn (xml method.Docs) method.Name (synType "HttpHandler")
                      
                      if not responseTypes.IsEmpty then
                          // Choice<{responseTypes[0]}, {responseTypes[1]}, ...>
                          // Or {responseType}
                          let returnType =
                              if responseTypes.Length > 1
                              then choiceOf responseTypes
                              else responseTypes.Head
                              
                          let respondsUnit = method.Responses |> List.map (fun x -> x.Kind) = [NoType]
                          
                          let fullInputReturnType =
                              maybeParams
                              // ({param} * HttpContext)
                              |> Option.map (fun param -> tuple [ param; synType "HttpContext" ])
                              // HttpContext
                              |> Option.defaultValue (synType "HttpContext")
                              
                          // helper for emitting:                                                                             
                          // override {implDefn} = fun next ctx ->task {                                                      
                          //     (*optional*) let query = ctx.TryBindQuery<TQuery>()
                          //     let! input = this.{method.Name}Input {argExpr}
                          //     return! this.{method.Name}Output input next ctx                                              
                          // }                                                                                                
                          let defaultImplementationEmitter implDefn (maybePath: TypeSchema option) =
                                let maybeQuery =
                                    method.Parameters
                                    |> Option.bind (fun x -> x |> Map.toSeq |> Seq.filter (fst >> ((=) Query)) |> Seq.map snd |> Seq.tryExactlyOne)
                                let maybeQueryBindingType =
                                    maybeQuery
                                    |> Option.map ^ fun q ->
                                        let tmpSchema = tmpBindingSchemasMap |> Map.tryFind (SourceType q.Name)
                                        tmpSchema, q
                                    
                                let queryBinding = "queryArgs"
                                let maybeBindQuery =
                                    maybeQueryBindingType
                                    |> Option.map ^ fun (tmpSchema, querySchema) ->
                                        let bindRaw =
                                            app
                                                (typeApp (longIdentExpr "ctx.TryBindQueryString") [tmpSchema |> Option.map (fun v -> v.GeneratedName) |> Option.defaultValue querySchema.Name |> synType])
                                                (longIdentExpr "System.Globalization.CultureInfo.InvariantCulture")
                                            ^|> Result.mapErrorExpr (identExpr CodeGenErrorsDU.errInnerGiraffeBinding ^>> identExpr CodeGenErrorsDU.errOuterQuery)
                                        tmpSchema
                                        |> Option.map ^ fun v ->
                                            bindRaw
                                            ^|> Result.mapExpr (DefaultsGeneration.generateDefaultMappingFunFromSchema tmpBindingSchemasMap v querySchema)
                                        |> Option.defaultValue bindRaw
                                        |> CodeGenNullChecking.bindNullCheckIntoResult "query" querySchema CodeGenErrorsDU.errOuterQuery
                                    |> Option.map ^ letExpr queryBinding []
                                
                                let pathBinding = "pathArgs"
                                let maybeBindPath =
                                    // use path args as result for future validation
                                    maybePath
                                    |> Option.map
                                        (
                                            fun p ->
                                                let res = typeApp (identExpr "Result") [extractResponseSynType (Some p.Name) p.Kind; synType CodeGenErrorsDU.errOuterTypeName]
                                                let okCall = SynExpr.DotGet(res,r,longIdentWithDots "Ok",r)
                                                let expr = app okCall (identExpr "pathArgs")
                                                CodeGenNullChecking.bindNullCheckIntoResult "path" p CodeGenErrorsDU.errOuterPath expr
                                        )
                                    |> Option.map ^ letExpr pathBinding []

                                let combinedInputs = "combinedArgs"
                                let rec generateBinds binded leftToBind generateFinal =
                                    if List.length leftToBind > 0 then
                                        identExpr binded
                                        ^|> Result.bindExpr
                                            ^ lambda ([simplePat binded] |> simplePats)
                                                ^ generateBinds leftToBind.Head leftToBind.Tail generateFinal
                                    else
                                        identExpr binded
                                            ^|> Result.mapExpr
                                                ^ lambda ([simplePat binded] |> simplePats) ^ generateFinal()
                                
                                let generateInputsCombination combinedRecordPropertyToOriginalValue synt (schema: TypeSchema) bindings =
                                    let finalGenerator () =
                                        letExprComplex
                                            (SynPat.Typed(SynPat.Named(SynPat.Wild r, ident "v", false, None, r), synt, r))
                                            (
                                                let bindings = Map bindings
                                                match schema.Kind with
                                                | TypeKind.Object o ->
                                                    [
                                                        for (name, _, _) in o.Properties do
                                                            let (sourceLocation, sourceName) = combinedRecordPropertyToOriginalValue |> Map.find name
                                                            let sourceBinding = bindings |> Map.find sourceLocation
                                                            name, longIdentExpr (sourceBinding + "." + sourceName)
                                                    ]
                                                | _ -> failwith "combined record should be a record, you know"
                                                |> recordExpr
                                            )
                                            (identExpr "v")
                                    let onlyNames = bindings |> List.map snd
                                    generateBinds onlyNames.Head onlyNames.Tail finalGenerator
                                    
                                let nonCombinedNonBodyArgs =
                                    [
                                        maybeBindPath |> Option.map ^ fun _ -> Path, pathBinding
                                        maybeBindQuery |> Option.map ^ fun _ -> Query, queryBinding
                                    ]
                                    |> List.choose id
                                    
                                let maybeBindCombined =
                                    Option.map2 (fun a b -> a,b) maybeCombinedType maybeCombinedTypeOpenApi
                                    |> Option.bind
                                        (
                                            fun (synt,schema) ->
                                                let combinedRecordPropertyToOriginalValue =
                                                    getCombinedRecordPropertyNamesFrom method.Parameters.Value
                                                    |> Seq.map (fun r -> r.CombinedRecordPropertyName, (r.OriginalLocation, r.OriginalName))
                                                    |> Map
                                                nonCombinedNonBodyArgs
                                                |> fun x -> if x.Length > 1 then Some x else None
                                                |> Option.map ^ generateInputsCombination combinedRecordPropertyToOriginalValue synt schema
                                        )
                                    |> Option.map ^ letExpr combinedInputs []
                                
                                let bodyBinding = "bodyArgs"
                                let maybeBodyBindingType =
                                    maybeBodyOpenApi
                                    |> Option.map ^ fun q ->
                                        let tmpSchema = tmpBindingSchemasMap |> Map.tryFind (SourceType (snd q).Name)
                                        tmpSchema, q
                                let maybeBindBody =
                                    maybeBodyBindingType
                                    |> Option.map ^ fun (tmpSchema, (location, bodySchema)) ->
                                        letBangExpr bodyBinding
                                            (
                                                let expr =
                                                    match location with
                                                    | Body contentType ->
                                                        match contentType with
                                                        | MediaType.Form -> "ctx.BindFormAsync"
                                                        | MediaType.Json -> "ctx.BindJsonAsync"
                                                        | v -> failwithf "Content type %A is not supported" v 
                                                    | _ -> failwith "Body should be located in body, you know"
                                                    |> longIdentExpr
                                                let typeApp = typeApp expr [tmpSchema |> Option.map (fun v -> v.GeneratedName) |> Option.defaultValue bodySchema.Name |> synType]
                                                let call = app typeApp (tupleExpr [])
                                                let bindRaw =
                                                    letBangExpr bodyBinding call (returnExpr ^ app (identExpr "Ok") (identExpr bodyBinding))
                                                let bindCallIntoResult =
                                                    tmpSchema
                                                    |> Option.map ^ fun v ->
                                                        bindRaw
                                                        ^|> Result.mapExpr (DefaultsGeneration.generateDefaultMappingFunFromSchema tmpBindingSchemasMap v bodySchema)
                                                    |> Option.defaultValue bindRaw
                                                    |> CodeGenNullChecking.bindNullCheckIntoResult "body" bodySchema CodeGenErrorsDU.errOuterBody
                                                let catchClause =
                                                    [
                                                        returnExpr (app (identExpr CodeGenErrorsDU.errInnerFormatterBindingExn) (identExpr "e"))
                                                        ^|> identExpr CodeGenErrorsDU.errOuterBody ^|> identExpr "Error" 
                                                        |> clause (SynPat.Named(SynPat.Wild r, ident "e", false, None, r))
                                                    ]
                                                taskBuilder
                                                ^ SynExpr.TryWith(bindCallIntoResult, r, catchClause, r, r, DebugPointAtTry.Yes r, DebugPointAtWith.Yes r)
                                            )
                                let nonCombinedBodyArgs =
                                    [
                                        maybeBodyOpenApi |> Option.map fst |> Option.map (fun l -> l, bodyBinding)
                                    ]
                                    |> List.choose id
                                
                                let finalArgsBinding = "args"
                                
                                let nonBody =
                                    nonCombinedNonBodyArgs
                                    |> List.tryExactlyOne
                                    |> Option.map snd
                                    |> Option.orElse (maybeCombinedType |> Option.map (fun _ -> combinedInputs))
                                let body = nonCombinedBodyArgs |> List.tryExactlyOne |> Option.map snd
                                                                
                                let maybeBindFinalArgs =
                                    Option.map2 (fun a b -> a,b) nonBody body
                                    |> Option.map ^ fun (nonBody, body) ->
                                        generateBinds nonBody [body] ^ fun () -> tupleExpr [nonBody; body]
                                    |> Option.orElse (body |> Option.orElse nonBody |> Option.map identExpr)
                                    |> Option.map ^ letExpr finalArgsBinding []
                                    |> Option.map ^ fun f continuation ->
                                        f
                                        ^
                                            let allRawBindings =
                                                nonCombinedBodyArgs
                                                |> Seq.append nonCombinedNonBodyArgs
                                                |> Seq.map snd
                                                |> Seq.map ^ fun result -> app (identExpr CodeGenErrorsDU.tryExtractErrorName) (identExpr result)
                                                |> Seq.toList
                                            if allRawBindings.Length = 1 then
                                                continuation
                                            else
                                                letExpr finalArgsBinding []
                                                    (
                                                        simpleValueMatching finalArgsBinding
                                                            [
                                                                "Ok", "v", app (identExpr "Ok") (identExpr "v")
                                                                "Error", "e",
                                                                    let errExpr =
                                                                        letExpr "errs" []
                                                                            (
                                                                                SynExpr.ArrayOrList(false, allRawBindings, r)
                                                                                ^|> seqChooseId
                                                                                ^|> longIdentExpr "Seq.toArray"
                                                                            )
                                                                            (
                                                                                paren
                                                                                ^ ifElseExpr
                                                                                      (
                                                                                          app (appI (identExpr "op_GreaterThan") (longIdentExpr "errs.Length")) (constExpr ^ SynConst.Int32 1)
                                                                                      )
                                                                                      (app (identExpr CodeGenErrorsDU.errOuterCombined) (identExpr "errs"))
                                                                                      (app (longIdentExpr "Array.head") (identExpr "errs"))
                                                                            )
                                                                    errExpr ^|> identExpr "Error"
                                                            ]
                                                    ) continuation
                                
                                let argExpr = identExpr "ctx"
                                
                                let finalCall =
                                    letBangExpr                                                                                 
                                      "input"                                                                                 
                                      (
                                          let sucMethod = sprintf "this.%sInput" method.Name |> longIdentExpr
                                          let errMethod = sprintf "this.%sInputError" method.Name |> longIdentExpr
                                          let allRawBindings = [ nonBody; body ] |> List.choose id
                                          if allRawBindings.Length = 0 then
                                              app sucMethod argExpr
                                          else
                                              matchExpr finalArgsBinding
                                                [
                                                    clause (SynPat.LongIdent(longIdentWithDots "Ok", None, None, Pats <| [tuplePat allRawBindings], None, r))
                                                    ^ app sucMethod (tupleExpr [ yield! allRawBindings; "ctx" ])
                                                    clause (synLongPat "Error" "e")
                                                    ^ app errMethod (tupleExpr ["e"; "ctx"])
                                                ]
                                      )                      
                                      (returnBang                                                                             
                                       ^ curriedCall (sprintf "this.%sOutput" method.Name)
                                             [
                                                 if respondsUnit then
                                                     "()"
                                                 else
                                                    "input"
                                                 "next"
                                                 "ctx"
                                             ])

                                let makeCall maybeBind finalCall =
                                    maybeBind
                                    |> Option.map (fun b -> b ^ finalCall)
                                    |> Option.defaultValue finalCall
                                
                                let finalCall =
                                    // the code below works like backpipe because each next call is applied as a callback to the previous one
                                    finalCall
                                    |> makeCall maybeBindFinalArgs
                                    |> makeCall maybeBindBody
                                    |> makeCall maybeBindCombined
                                    |> makeCall maybeBindPath
                                    |> makeCall maybeBindQuery
                                
                                implDefn                                                                                      
                                ^ lambdaFunNextCtxExpr                                                                        
                                ^ taskBuilder                                                                                 
                                ^ finalCall
                                  
                          // emitting httpHandler default implementation method or property
                          let defaultHttpHandler =        
                              maybePath
                              |> Option.map ^ fun _ ->
                                    // override this.{method.Name} pathArgs = fun next ctx ->task {
                                    //     let! input = this.{method.Name}Input(args, ctx)
                                    //     return! this.{method.Name}Output input next ctx
                                    // }
                                    defaultImplementationEmitter
                                        (methodImplDefn method.Name ["pathArgs"])
                              |> Option.defaultWith ^ fun _ ->
                                    // override this.{method.Name} = fun next ctx ->task {
                                    //     let! input = this.{method.Name}Input ctx
                                    //     return! this.{method.Name}Output input next ctx
                                    // }
                                    defaultImplementationEmitter
                                        (methodImplDefn method.Name [])
                          defaultHttpHandler maybePathOpenApi
                          
                          // abstract {method.Name}Input: {fullReturnType} -> Task<{returnType}>
                          abstractMemberDfn xmlEmpty (method.Name + "Input") (fullInputReturnType ^-> taskOf [ returnType ])
                          if maybeParams.IsSome then
                              let errorHandlerName = method.Name + "InputError"
                              // abstract {method.Name}InputError: error * HttpContext -> Task<{returnType}>
                              abstractMemberDfn xmlEmpty errorHandlerName (tuple [synType CodeGenErrorsDU.errOuterTypeName; synType "HttpContext"] ^-> taskOf [ returnType ])
                              methodImplDefn errorHandlerName ["t"]
                                (
                                    letExprComplex (tuplePat ["err"; "http"]) (identExpr "t")
                                    ^ letExpr "err" [] (app (app (identExpr CodeGenErrorsDU.outerErrToStringName) (constExpr <| SynConst.Int32 0)) (identExpr "err"))
                                    ^ app (typeApp (longIdentExpr "Task.FromException") [returnType]) (paren <| app (identExpr "exn") ("err" |> identExpr))
                                )
                          // abstract {method.Name}Output: {returnType} -> HttpHandler
                          abstractMemberDfn xmlEmpty (method.Name + "Output") (returnType ^-> synType "HttpHandler")
                          
                          // giraffe handler for particular response
                          let response2handler (response: Response) inputBinding =
                                let contentHandler =
                                    // currently everything goes to json
                                    match response.MediaType with
                                    | Json
                                    | NotSpecified -> app (identExpr "json" ) (identExpr inputBinding)
                                    | Form -> app (identExpr "form" ) (identExpr inputBinding)
                                    | Other x -> failwithf "Emitting of code for media type %s currently not supported" x
                                
                                if response.Code = 200
                                then
                                    contentHandler
                                else
                                    setStatusCodeExpr response.Code >=> contentHandler
                          
                          // match generator for different responses
                          let methodResponseToClause (responses: Response list): SynMatchClause list =
                              let patName n = sprintf "Choice%dOf%d" n responses.Length
                              responses
                              |> List.mapi ^fun i response ->
                                  let i = i + 1
                                  let patBinding = sprintf "responseOn%d" response.Code
                                  synLongPat (patName i) patBinding ^=> response2handler response patBinding
                          
                          // body for default implementation of Output method
                          let body = 
                              if method.Responses.Length > 1 then
                                matchExpr "input" ^methodResponseToClause method.Responses
                              else
                                response2handler method.Responses.Head (if respondsUnit then "()" else "input")
                          
                          // override this.{method.Name}Output input =
                          //    match input with
                          //    | Choice1Of2 array -> json array
                          //    | Choice2Of2 () -> setStatusCode 404 }
                          methodImplDefn (method.Name + "Output") [if not respondsUnit then "input" else "()"] body ]

          let routes = api.Paths |> List.map createRoute

          let routesExpr =
              if routes.Length > 1 then chooseExpr routes else routes.[0]

          letHttpHandlerDecl "webApp"
          ^ taskBuilder
          ^ letGetServiceDecl
          ^ returnBang
          ^ appNextCtx routesExpr ]

/// Creating source code string from provided AST using default Fantomas settings
let sourceCode ast =

    let dummyInput =
        ParsedImplFileInput.ParsedImplFileInput
            ("", false, QualifiedNameOfFile.QualifiedNameOfFile(Ident("", r)), [], [], [ ast ], (true, true))

    let dummyImplFile = ParsedInput.ImplFile(dummyInput)

    CodeFormatter.FormatASTAsync
        (dummyImplFile,
         "abc.fs",
         [],
         None,
         { Fantomas.FormatConfig.FormatConfig.Default with
               StrictMode = true })
    |> Async.RunSynchronously
