namespace GiraffeGenerator.IntegrationTests

open System.Collections.Generic
open System.Net
open System.Net.Http
open System.Text
open FSharp.Control.Tasks.V2.ContextInsensitive
open System
open Giraffe
open Microsoft.AspNetCore
open Microsoft.AspNetCore.Builder
open Microsoft.AspNetCore.Hosting
open Microsoft.AspNetCore.TestHost
open Microsoft.Extensions.DependencyInjection
open Microsoft.Extensions.Logging
open Xunit

type SpecWithArgumentsTests() =
    
    let specWithArgumentsService=
        { new SpecwithargumentsAPI.Service() with
            
            member _.ListSearchableFieldsInput ((args,ctx)) = task {
                return
                    if args.version = "v1" then
                        Choice1Of2 "ok"
                    elif args.dataset = "foo" then
                        Choice1Of2 "good"
                    else
                        Choice2Of2 "not_ok"
                }
            
            member _.PerformSearchInput ((args,body,ctx)) = task {
                return
                    if args.version = "v1" then
                        Choice1Of2 [| box "abc" |]
                    elif args.dataset = "foo" then
                        Choice1Of2 [| box "good" |]    
                    else
                        Choice2Of2 ()
                }
            
            member _.OnlyPathParametersInput ((args, ctx)) = task {
                    return [|args.dataset; args.version|]
                }
            member _.OnlyQueryParametersInput ((args, ctx)) = task {
                    return [|args.dataset; args.version|]
                }
            member _.OnlyFormParametersInput ((args, ctx)) = task {
                    return [|args.dataset; args.version|]
                }
            member _.OnlyJsonParametersInput ((args, ctx)) = task {
                    return [|args.dataset; args.version|]
                }
            }
        
    let configureApp (app : IApplicationBuilder) =
        app.UseGiraffe SpecwithargumentsAPI.webApp

    let configureServices (services : IServiceCollection) =
        services
            .AddGiraffe()
            .AddSingleton(specWithArgumentsService)
        |> ignore

    let configureLogging (loggerBuilder : ILoggingBuilder) =
        loggerBuilder.AddFilter(fun lvl -> lvl.Equals LogLevel.Error)
                     .AddConsole()
                     .AddDebug() |> ignore

    let webHostBuilder =
        WebHost.CreateDefaultBuilder()
            .Configure(Action<IApplicationBuilder> configureApp)
            .ConfigureServices(configureServices)
            .ConfigureLogging(configureLogging)
            
    let server = new TestServer(webHostBuilder)
    let client = server.CreateClient()

    [<Fact>]
    let ``GET /abc/v1/fields -> OK "ok"``() = task {
        let! response = client.GetAsync("/abc/v1/fields")
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("\"ok\"",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }
    
    [<Fact>]
    let ``GET /foo/v2/fields -> OK "good"``() = task {
        let! response = client.GetAsync("/foo/v2/fields")
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("\"good\"",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }
    
    [<Fact>]
    let ``GET /abc/v3/fields -> NOT_FOUND``() = task {
        let! response = client.GetAsync("/abc/v3/fields")
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal(HttpStatusCode.NotFound, response.StatusCode)
    }
    
    [<Fact>]
    let ``POST /abc/v1/records -> OK ["abc"]``() = task {
        use content = new FormUrlEncodedContent(Seq.empty)
        let! response = client.PostAsync("/abc/v1/records", content)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("[\"abc\"]",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }
    
    [<Fact>]
    let ``POST /foo/v2/records -> OK ["good"]``() = task {
        use content = new FormUrlEncodedContent(Seq.empty)
        let! response = client.PostAsync("/foo/v2/records", content)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("[\"good\"]",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }
    
    [<Fact>]
    let ``POST /abc/v3/records -> NOT_FOUND``() = task {
        use content = new FormUrlEncodedContent(Seq.empty)
        let! response = client.PostAsync("/abc/v3/records", content)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal(HttpStatusCode.NotFound, response.StatusCode)
    }

    [<Fact>]
    let ``POST /foo/v2/only-path-parameters -> OK ["foo", "v2"]``() = task {
        let! response = client.PostAsync("/foo/v2/only-path-parameters", null)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("[\"foo\",\"v2\"]",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }

    [<Fact>]
    let ``POST /only-query-parameters?dataset=foo&version=v2 -> OK ["foo", "v2"]``() = task {
        let! response = client.PostAsync("/only-query-parameters?dataset=foo&version=v2", null)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("[\"foo\",\"v2\"]",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }

    [<Fact>]
    let ``POST /only-form-parameters (FormUrlEncoded dataset=foo&version=v2) -> OK ["foo", "v2"]``() = task {
        let content =
            seq {
                "dataset", "foo"
                "version", "v2"
            }
            |> Seq.map KeyValuePair
        use content = new FormUrlEncodedContent(content)
        let! response = client.PostAsync("/only-form-parameters", content)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("[\"foo\",\"v2\"]",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }

    [<Fact>]
    let ``POST /only-json-parameters (JSON {"dataset":"foo","version":"v2"}) -> OK ["foo", "v2"]``() = task {
        let content = """{"dataset":"foo","version":"v2"}"""
        use content = new StringContent(content, Encoding.UTF8, "application/json")
        let! response = client.PostAsync("/only-json-parameters", content)
        let! text = response.Content.ReadAsStringAsync()
        Assert.Equal("[\"foo\",\"v2\"]",text)
        Assert.Equal(HttpStatusCode.OK, response.StatusCode)
    }

    interface IDisposable with
        member _.Dispose() = server.Dispose()

