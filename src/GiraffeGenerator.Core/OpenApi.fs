module OpenApi

open System
open Microsoft.OpenApi.Any
open Microsoft.OpenApi.Models
open Microsoft.OpenApi.Readers
open System.IO
open System.Text.RegularExpressions

let inline trimLower (s: string) =
    if isNull s then None else
    s.Trim().ToLowerInvariant() |> Some

let inline splitLine (str: string) =
    str.Split('\n')
    |> Seq.toList

type Docs =
    { Summary: string list option
      Remarks: string list option
      Example: string list option }
    static member Create(summary, remarks, example: IOpenApiAny) =
        match Option.ofObj summary, Option.ofObj remarks, Option.ofObj example with
        | None, None, None -> None
        | summary, remarks, example ->
            { Summary = summary |> Option.map splitLine
              Remarks = remarks |> Option.map splitLine
              Example = example |> Option.map (string >> splitLine) }
            |> Some
        
/// Formats for string type.
/// URI is not standard, but included
/// It could be anything
type StringFormat =
    | String
    | Byte
    | Binary
    | DateString
    | DateTimeString
    | PasswordString
    | Custom of string
    
    static member Parse (maybeFormat: string Option) =
        if maybeFormat.IsNone then String else
        match maybeFormat.Value with
        | "byte" -> Byte
        | "binary" -> Binary
        | "date" -> DateString
        | "date-time" -> DateTimeString
        | "password" -> PasswordString
        | x -> Custom x
        
/// Active patterns to quickly determine what type OpenApiSchema represents
let (|ArrayKind|ObjectKind|PrimKind|) (schema: OpenApiSchema) =
    match trimLower schema.Type with
    | Some "array"  | None when not (isNull schema.Items)      -> ArrayKind  schema.Items
    | Some "object" | None when not (isNull schema.Properties) -> ObjectKind schema
    | Some primType -> PrimKind primType
    | _ -> failwithf "unexpected type of schema: %A" schema.Type
        
/// All primitive type kinds for a fields in type definitions
type PrimTypeKind =
    | Int
    | Long
    | Double
    | Bool
    | Any
    | String of StringFormat
    
    static member Parse (typeKind: string, format: string) =
        
        match trimLower typeKind, trimLower format with
        | Some "integer", Some "int64" -> Long 
        | Some "integer", _ -> Int
        | Some "number", _ -> Double
        | Some "boolean", _ -> Bool
        | Some "string", maybeStringFormat -> String(StringFormat.Parse maybeStringFormat)
        | _ -> failwithf "Unexpected type: %s and format: %A" typeKind format
        
    member s.GetDefaultLiteral (value: IOpenApiPrimitive) =
        let fw t = failwithf "%s literal has been found for non-%s type" t t
        let inline oneWay kind (value: ^v) (toDefault: ^t -> DefaultableKind) =
            match s with
            | x when x = kind ->
                let v = (^v:(member Value: ^t) value)
                toDefault v
            | _ -> fw (value.GetType().Name)
            
        match value with
        | :? OpenApiInteger as int ->
            match s with
            | Int -> DefaultableKind.Integer int.Value
            | Long -> DefaultableKind.Long (int64 int.Value)
            | _ -> fw "integer"
        | :? OpenApiLong as long ->
            match s with
            | Int ->  DefaultableKind.Long (int64 long.Value) 
            | Long -> DefaultableKind.Long long.Value
            | _ -> fw "int64"
        | :? OpenApiDouble as double -> oneWay Double double DefaultableKind.Double
        | :? OpenApiBoolean as bool -> oneWay Bool bool DefaultableKind.Boolean
        | :? OpenApiDateTime as dateTime -> oneWay (String DateTimeString) dateTime DefaultableKind.DateTime
        | :? OpenApiDate as date -> oneWay (String DateString) date DefaultableKind.Date
        | :? OpenApiPassword as pwd -> oneWay (String PasswordString) pwd DefaultableKind.String
        | :? OpenApiString as str ->
            match s with
            | String s ->
                let inline oneWay x = oneWay (String s) x
                match s with
                | PasswordString
                | StringFormat.String -> oneWay str DefaultableKind.String
                | Custom "uri"
                | Custom "uriref" -> oneWay {| Value = System.Uri str.Value |} DefaultableKind.Uri
                | Custom "uuid"
                | Custom "guid"
                | Custom "uid" -> oneWay {| Value = Guid.Parse str.Value |} DefaultableKind.Guid
                | _ -> oneWay str DefaultableKind.String
            | _ -> fw "string"
        | v -> failwith (sprintf "%A literals aren't supported for kind %A" v s)

and DefaultableKind =
    | String of string
    | Integer of int
    | Long of int64
    | Date of DateTime
    | DateTime of DateTimeOffset
    | Double of double
    | Boolean of bool
    | Uri of Uri
    | Guid of Guid

/// IR for object schemas
and ObjectKind =
    { Name: string option
      Properties: (string * TypeKind * Option<DefaultableKind>) list
      Docs: Docs option }
    
    static member private OptionIfNotRequired isRequired kind =
        if isRequired then kind
        else
            match kind with
            | TypeKind.Option v -> TypeKind.Option v
            | v -> TypeKind.Option v 
    
    static member Create(schema: OpenApiSchema) =
        let name =
            Option.ofObj schema.Reference
            |> Option.map (fun x -> x.Id)
            |> Option.orElseWith(fun _ -> Option.ofObj schema.Title)
        let fields =
            [
                for KeyValue(typeName, internalSchema) in schema.Properties ->
                    let internalType, def = TypeKind.Parse internalSchema
                    let internalType = ObjectKind.OptionIfNotRequired (schema.Required.Contains typeName || def.IsSome) internalType
                    typeName, internalType, def
            ]
        
        { Name = name
          Properties = fields
          Docs = Docs.Create(schema.Description, null, schema.Example) }
        
    static member Create(name: string, parameters: OpenApiParameter seq) =
        let fields =
            [ for param in parameters ->
                let kind, def = TypeKind.Parse param.Schema
                let kind = ObjectKind.OptionIfNotRequired (param.Required || def.IsSome) kind
                param.Name, kind, def ]
            
        { Name = Some name
          Properties = fields
          Docs = None }
and DUCaseKind =
    {
        Docs: Docs option
        CaseName: string option
        Kind: TypeKind
    }
and DUKind =
    {
        Name: string
        Cases: DUCaseKind list
        Docs: Docs option
    }
/// Kind of types for fields in schemas
/// Either primitive or Array<T> or Option<T> or Object with properties or DU
/// Array, Option and Object could recursively contains similar types
and TypeKind =
    | Prim of PrimTypeKind
    | Array of TypeKind * Option<DefaultableKind>
    | Option of TypeKind
    | Object of ObjectKind
    | DU of DUKind
    | BuiltIn of string
    | NoType
    static member Parse(schema: OpenApiSchema): TypeKind * DefaultableKind option =
        if isNull schema then Prim PrimTypeKind.Any, None
        else
            let kind, def =
                match schema with
                | ArrayKind items ->
                    let arrItm, def = TypeKind.Parse items
                    let isObj = match arrItm with | TypeKind.Object _ -> true | _ -> false 
                    if def.IsSome && isObj then
                        failwith "Default values aren't supported for entire objects"
                    Array (arrItm, def), None
                | ObjectKind schema ->
                    if schema.Default <> null then
                        failwith "Default values aren't supported for entire objects"
                    else
                        ObjectKind.Create(schema) |> Object, None
                | PrimKind primType ->
                    let prim = PrimTypeKind.Parse(primType, schema.Format)
                    let def = schema.Default |> Option.ofObj |> Option.map (fun x -> x:?>IOpenApiPrimitive) |> Option.map prim.GetDefaultLiteral
                    Prim prim, def
            if schema.Nullable && def.IsNone then
                (Option kind), None
            else kind, def

/// Representation of schema from OpenAPI
and TypeSchema =
    { Name: string
      Kind: TypeKind
      Docs: Docs option
      DefaultValue: DefaultableKind option }
    
    member private schema.DedupeTypeNames() =
        let obj =
            match schema.Kind with
            | TypeKind.Object o -> Some o
            | _ -> None
        let name =
            obj
            |> Option.bind (fun x -> x.Name)
            |> Option.defaultValue schema.Name
        let kind =
            obj
            |> Option.map (fun x -> { x with Name = Some name }) 
            |> Option.map TypeKind.Object
            |> Option.defaultValue schema.Kind
        {
            schema with
                Name = name
                Kind = kind
        }
    
    static member Parse(name, schema: OpenApiSchema): TypeSchema =
        let kind, def = TypeKind.Parse schema
        { Name = name
          Kind = kind
          DefaultValue = def
          Docs = Docs.Create(schema.Description, null, schema.Example) }.DedupeTypeNames()
        
    static member Parse(name, parameters: OpenApiParameter seq): TypeSchema =
        { Name = name
          Kind = TypeKind.Object (ObjectKind.Create (name, parameters))
          DefaultValue = None
          Docs = None }.DedupeTypeNames()

/// Supported response media types
type MediaType =
    | Json
    | Form
    | NotSpecified
    | Other of string

/// Typed response with corresponding HTTP code, media type and content type
type Response =
    { Code: int
      MediaType: MediaType
      Kind: TypeKind }

/// Source of binding
type PayloadNonBodyLocation =
    // TODO: Cookie (#35)
    | Path
    | Query
    // TODO Header (#35)
    with
        static member FromParameterLocation =
            function
            | ParameterLocation.Query -> Query
            | ParameterLocation.Path -> Path
            | _ -> Query

/// Endpoint call with name (should be unique across whole API at the moment) and method attached
type PathMethodCall =
    { Method: string
      Name: string
      Responses: Response list
      BodyParameters: (MediaType*TypeSchema) array option
      OtherParameters: Map<PayloadNonBodyLocation, TypeSchema> option
      Docs: Docs option }

/// Representation of OpenApi path with methods attach
/// e.g.: "/v2/item" with GET and SET
type ParsedPath =
    { Route: string
      Methods: PathMethodCall list
      Docs: Docs option }

/// Representation of a whole spec
type Api =
    { Name: string
      Paths: ParsedPath list
      Schemas: TypeSchema list
      Docs: Docs option }

let reader = OpenApiStringReader()

/// read openApiSpec by filePath
/// returning tuple with parsed document and diagnostic errors
let read file =
    File.ReadAllText file |> reader.Read

let inline private parseCode x =
    let isSuccess, result = System.Int32.TryParse x
    if isSuccess then result
    else failwith "Other types of `responses` map key rather than INTEGER are not supported"

let inline private parseMediaType x =
    match trimLower x with
    | Some "application/json" -> Json
    | Some "application/x-www-form-urlencoded" -> MediaType.Form
    | Some x -> Other x
    | None -> failwith "Media type can't be null!"
    
let private parseResponses (operation: OpenApiOperation) =
    [ for KeyValue(code, response) in operation.Responses do
        for KeyValue(mediaType, content) in response.Content do
            yield { Code = parseCode code
                    MediaType = parseMediaType mediaType
                    Kind = TypeKind.Parse content.Schema |> fst } ]

let private normalizeName =
    let regex = Regex("[_\.-]([a-z])", RegexOptions.Compiled)
    let firstCharRegex = Regex("(^.)", RegexOptions.Compiled)
    fun str ->
        let s = regex.Replace(str, fun (m: Match) -> m.Groups.[1].Value.ToUpper())
        firstCharRegex.Replace(s, fun m -> m.Groups.[0].Value.ToUpper())

/// Parse OpenApi document into our representation of it
/// Returning API name and list of ParsedPaths
let parse (doc: OpenApiDocument): Api =

    let title = doc.Info.Title.Replace(" ", "")
    
    let schemas =
        [ if not (isNull doc.Components) then
            for KeyValue(typeName, schema) in doc.Components.Schemas ->
                TypeSchema.Parse(typeName, schema) ]

    let paths =
        [ for KeyValue(route, path) in doc.Paths do
            let methods =
                [ for KeyValue(method, op) in path.Operations do
                    
                    let methodName = normalizeName (string method)
                    let opName = normalizeName op.OperationId
                    
                    let pathParameters = Option.ofObj path.Parameters |> Option.map Seq.toArray
                    let operationParameters = Option.ofObj op.Parameters |> Option.map Seq.toArray
                    let allParameters =
                        Option.map2 Array.append pathParameters operationParameters
                        |> Option.orElse operationParameters
                        |> Option.orElse pathParameters
                    let nonBodyParameters =
                        allParameters
                        |> Option.filter (fun x -> x.Length > 0)
                        |> Option.map
                            (fun parameters ->
                                parameters
                                |> Seq.groupBy (fun x -> Option.ofNullable x.In |> Option.defaultValue ParameterLocation.Query |> PayloadNonBodyLocation.FromParameterLocation)
                                |> Seq.map (fun (location, parameters) ->
                                    location, TypeSchema.Parse(methodName + opName + location.ToString(), parameters))
                                |> Map
                            )

                    let bodyParameters =
                        op.RequestBody
                        |> Option.ofObj
                        |> Option.map (fun rb ->
                            rb.Content
                            |> Seq.map (fun (KeyValue(mt, body)) ->
                                let mediaType = parseMediaType mt
                                let name = opName + methodName + "Body" + mediaType.ToString()
                                let schema = TypeSchema.Parse(name, body.Schema)
                                mediaType, schema)
                            |> Seq.toArray)
                        
                        
                    let responses =
                        [ for KeyValue(code, response) in op.Responses do
                            if response.Content.Count > 0 then
                                for KeyValue(mediaType, content) in response.Content do
                                    { Code = parseCode code
                                      MediaType = parseMediaType mediaType
                                      Kind = TypeKind.Parse content.Schema |> fst }
                            else
                                { Code = parseCode code
                                  MediaType = NotSpecified
                                  Kind = NoType } ]
                        
                    if responses.Length > 7 then
                        failwith "There could be only 7 or lower combinations of (mediaType * responseCode) per one path"
                    
                    { Method = methodName
                      Name = opName
                      Responses = responses
                      BodyParameters = bodyParameters
                      OtherParameters = nonBodyParameters
                      Docs = Docs.Create(op.Description, op.Summary, null) } ]
                
            yield { Route = route
                    Methods = methods
                    Docs = Docs.Create(path.Description, path.Summary, null) } ]
        
    { Name = title
      Paths = paths
      Schemas = schemas
      Docs = Docs.Create(doc.Info.Description, null, null)} 
