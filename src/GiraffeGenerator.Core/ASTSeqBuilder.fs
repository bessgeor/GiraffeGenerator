module ASTSeqBuilder
    open FSharp.Compiler.SyntaxTree
    open AST

    let yieldFromExpr body =
        SynExpr.YieldOrReturnFrom((true, false), body, r)
    
    let seqCEExprList =
        function
        | [ singleExpr ] -> singleExpr
        | l -> seqExprs l
            
    let seqCEExpr body =
        let body = SynExpr.CompExpr(false, ref true, body, body.Range)
        app (identExpr "seq") body


