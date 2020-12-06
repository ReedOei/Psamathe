requires "pure-flow-common.k"

module SOLIDITY-SYNTAX
    imports DOMAINS-SYNTAX
    imports VARS


    syntax SolVar ::= SolType Var
    syntax SolArgs ::= List{SolVar, ","}

    syntax SolVarDef ::= SolVar ";"
    syntax SolVarDefs ::= List{SolVarDef, ""}

    syntax Access ::= Var
                    | Expr "." Var
    syntax Expr ::= Bool | Int | Access
                  | Expr "++"
                  | Expr "(" Exprs ")"
                  | Expr "[" Expr "]"
                  | Var "(" "{" SolFields "}" ")"
                  > left: Expr "+" Expr
                  | Expr "-" Expr
                  | Expr "||" Expr
                  > nonassoc: Expr "<" Expr
                  | Expr "==" Expr
    syntax Exprs ::= List{Expr, ","}

    syntax SolField ::= Var ":" Expr
    syntax SolFields ::= List{SolField, ","}

    syntax SolStmt ::= Expr ";"
                     | SolVar "=" Expr ";"
                     | SolVarDef
                     | Expr "=" Expr ";"
                     | "delete" Expr ";"
                     | "return" Var ";"
                     | "for" "(" SolStmt Expr ";" Expr ")" "{" SolStmts "}"
                     | "try" Expr "returns" "(" SolVar ")" "{" SolStmts "}" "catch" "{" SolStmts "}"
                     | "if" "(" Expr ")" "{" SolStmts "}"
    syntax SolStmts ::= ".SolStmts"
                      | SolStmt
                      | SolStmts SolStmts [assoc, right]
                      // List{SolStmt, ""} [klabel(stmts)]

    syntax SolType ::= Var
                     | SolType "[]"
                     | "mapping" "(" SolType "=>" SolType ")"

    syntax Struct ::= "struct" Var "{" SolVarDefs "}"
    syntax Function ::= "function" Var "(" SolArgs ")" "returns" "(" SolVar ")" "{" SolStmts "}"
    syntax Constructor ::= "constructor" "(" SolArgs ")" "{" SolStmts "}"

    syntax SolDecl ::= Struct | Function | Constructor | SolVarDef

    syntax SolDecls ::= List{SolDecl, ""}
    syntax Contract ::= "contract" Var "{" SolDecls "}"
endmodule

module PURE-FLOW-COMPILER-SYNTAX
    imports PURE-FLOW-COMMON-SYNTAX
endmodule

module PURE-FLOW-COMPILER
    imports PURE-FLOW-COMPILER-SYNTAX
    imports SOLIDITY-SYNTAX
    imports DOMAINS
    imports COLLECTIONS
    imports PURE-FLOW-COMMON

    syntax SourceList ::= source(List)
                        | sourceSelect(Located, Located)
                        | sourceFilter(Located, TypeQuant, Var, Locateds)
    syntax Located ::= Var
                     | SourceList
                     | guardSelect(Located, Located)
                     | filterInto(TypeQuant, Var, Locateds, Located)
    syntax Locateds ::= List{Located, ","} [klabel(locators)]
                      | Vars
    syntax Locators ::= Locateds
    syntax Locator ::= Located
    syntax KResult ::= Located
                     | Vars

    // Variables we'll need to do code generation
    syntax Var ::= "success" | "keys" | "underlying_map" | "length" | "push"

    configuration
        <common />
        <typeNameMap> .Map </typeNameMap>
        <structs> .Map </structs>
        <fields> .Map </fields>
        <solFunctions> .Map </solFunctions>
        <compiled> .List </compiled>
        <typeEncoding> .Map </typeEncoding>
        <tempVars> .Set </tempVars>

    syntax KItem ::= translateDecl(Decl)
                   | "done"

    // =========================================
    // Sequencing
    // =========================================
    rule .Stmts => . [structural]
    rule S1:Stmt Rest:Stmts => S1 ~> Rest [structural]

    rule D:Decl => translateDecl(D)

    syntax SolDecls ::= List2SolDecls(List) [function, functional]
    rule List2SolDecls(.List) => .SolDecls
    rule List2SolDecls(ListItem(D:SolDecl) Rest) => D List2SolDecls(Rest)

    // =========================================
    // Scoping
    // =========================================

    syntax KItem ::= "newScope"
    rule <k> newScope => . ... </k>
        <compiled> .List => ListItem(.SolStmts) ... </compiled>

    // =========================================
    // Entry point
    // =========================================

    rule run(Stmts) => newScope ~> Stmts ~> done

    rule <k> done
             =>
            contract String2Id("C") {
                List2SolDecls(
                    values(Structs)
                    values(Functions)
                    ListItem(
                        constructor( .SolArgs ) {
                            Body
                        }
                    )
                )
            }
         </k>
        <compiled> ListItem(Body) => .List </compiled>
        <structs> Structs </structs>
        <solFunctions> Functions </solFunctions>

    rule <k> translateDecl(type T is Ms BaseT) => . ... </k>
        <structs> Structs => Structs defineStructs(T, BaseT) </structs>
        <types> ... .Map => T |-> typeDef(modifiersToSet(Ms), BaseT) ... </types>
        <typeEncoding> ... .Map => T |-> encodeType(T, BaseT) ... </typeEncoding>

    syntax KItem ::= setupArgs(VarDefs)
                   | defFunc(Var, VarDefs, Var, BaseType)
                   | cleanupEnv(Set)

    rule translateDecl(transformer F(Args) -> X : _ T { Body })
        => newScope ~>
           setupArgs(X : empty T, Args) ~>
           Body ~>
           defFunc(F, Args, X, T) ~>
           cleanupEnv(keys(makeEnv(X : empty T, Args)))

    rule setupArgs(.VarDefs) => .
    rule <k> setupArgs(X : _ T, Rest) => setupArgs(Rest) ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <compiled> ListItem(Ss:SolStmts => Ss (baseTypeToSolType(T) X;)) ... </compiled>

    syntax SolArgs ::= varDefsToSolArgs(VarDefs) [function, functional]
    rule varDefsToSolArgs(.VarDefs) => .SolArgs
    rule varDefsToSolArgs(X : _ T, Rest) => baseTypeToSolType(T) X, varDefsToSolArgs(Rest)

    rule <k> defFunc(F, Args, RetVar, RetType) => . ... </k>
        <solFunctions>
            ...
            .Map =>
            F |->
            function F(varDefsToSolArgs(Args)) returns (baseTypeToSolType(RetType) RetVar) {
                Body
            }
            ...
        </solFunctions>
        <compiled> ListItem(Body) => .List ... </compiled>

    rule <k> cleanupEnv(Xs) => . ... </k>
        <typeEnv> Env => removeAll(Env, Xs) </typeEnv>

    syntax Map ::= defineStructs(Var, BaseType) [function, functional]
                 | defineVarDefsStructs(VarDefs) [function, functional]

    rule defineStructs(_, nat) => .Map
    rule defineStructs(_, string) => .Map
    rule defineStructs(_, address) => .Map
    rule defineStructs(_, bool) => .Map
    rule defineStructs(_, _:Var) => .Map
    rule defineStructs(T, record(_) { Fields }) => (T |-> struct T { encodeFields(Fields) }) defineVarDefsStructs(Fields)
    rule defineStructs(T, map _ T1 => _ T2) => T |-> struct T {
                                                        mapping (baseTypeToSolType(T1) => baseTypeToSolType(T2)) underlying_map;
                                                        baseTypeToSolType(T1)[] keys;
                                                     }
    rule defineStructs(_, table(.Vars) _ T) => defineStructs(nameOf(T), T)

    rule defineVarDefsStructs(.VarDefs) => .Map
    rule defineVarDefsStructs(_ : _ T, Rest) => defineStructs(nameOf(T), T) defineVarDefsStructs(Rest)
    /* rule defineVarDefsStructs(_ : T:BaseType, Rest) => defineStructs(nameOf(T), T) defineVarDefsStructs(Rest) */

    rule try { S1 } catch { S2 } => newScope ~> S1 ~> newScope ~> S2 ~> tryCatch
    syntax KItem ::= "tryCatch"

    syntax KItem ::= test(K)

    rule <k> tryCatch => newClosure(!I, Env, TryBlock) ... </k>
        <typeEnv> Env </typeEnv>
        <compiled>
            ListItem(TryBlock) ListItem(CatchBlock) ListItem(ParentScope)
            => ListItem(ParentScope
                packScope(genVar(!J), Env)
                (try this.(closureName(!I))(genVar(!J)) returns (closureTypeName(!I) genVar(!K)) {
                    unpackScope(genVar(!K), Env)
                } catch {
                    CatchBlock
                }))
            ... </compiled>
        <structs> Structs => union(Structs, closureStruct(!I, Env)) </structs>

    syntax KItem ::= newClosure(Int, Map, SolStmts)
    rule <k> newClosure(I, Env, Body) => . ... </k>
        <solFunctions> ... .Map => closureName(I) |->
                function closureName(I)(closureTypeName(I) genVar(!J)) returns (closureTypeName(I) genVar(!K)) {
                    unpackNewScope(genVar(!J), Env)
                    Body
                    packScope(genVar(!K), Env)
                }
            ...
        </solFunctions>

    syntax Map ::= closureStruct(Int, Map) [function, functional]
    rule closureStruct(I, M)
         => closureTypeName(I) |->
                struct closureTypeName(I) {
                    mapToSolVars(M)
                }

    syntax SolVarDefs ::= mapToSolVars(Map) [function, functional]
    rule mapToSolVars(.Map) => .SolVarDefs
    rule mapToSolVars((X |-> T) M) => baseTypeToSolType(T) X; mapToSolVars(M)

    syntax SolStmts ::= packScope(Var, Map) [function, functional]
    rule packScope(_, .Map) => .SolStmts
    rule packScope(X, (Y |-> _) Env) => X.Y = Y; packScope(X, Env)

    syntax SolStmts ::= unpackScope(Var, Map) [function, functional]
    rule unpackScope(_, .Map) => .SolStmts
    rule unpackScope(X, (Y |-> _) Env) => Y = X.Y; unpackScope(X, Env)

    syntax SolStmts ::= unpackNewScope(Var, Map) [function, functional]
    rule unpackNewScope(_, .Map) => .SolStmts
    rule unpackNewScope(X, (Y |-> T) Env) => baseTypeToSolType(T) Y = X.Y; unpackNewScope(X, Env)

    syntax Var ::= closureTypeName(Int) [function, functional]
    rule closureTypeName(I) => String2Id("closure_type_" +String Int2String(I))

    syntax VarDefs ::= mapToVarDefs(Map) [function, functional]
    rule mapToVarDefs(.Map) => .VarDefs
    rule mapToVarDefs((X |-> T) M) => X : T, mapToVarDefs(M)

    syntax Var ::= closureName(Int) [function, functional]
    rule closureName(I) => String2Id("closure_" +String Int2String(I))

    syntax KItem ::= flow(Locator, Locator) [seqstrict]
    rule <k> A --> B => flow(locate(A), locate(B)) ... </k>

    syntax KItem ::= "cleanTemp"
    rule <k> cleanTemp => . ... </k>
        <typeEnv> Env => removeAll(Env, Temps) </typeEnv>
        <tempVars> Temps => .Set </tempVars>

    syntax SolStmts ::= receiveValue(Expr, Located) [function, functional]

    syntax KItem ::= sendValues(Located, Located)

    rule flow(Src, Dst) => sendValues(Src, Dst) ~> cleanTemp

    rule <k> sendValues(Src, Dst) => . ... </k>
        <typeEnv> ... Src |-> nat ... </typeEnv>
        <compiled> ListItem(Cur => (Cur receiveValue(Src, Dst))) ... </compiled>
    rule <k> sendValues(Src, Dst) => . ... </k>
        <typeEnv> ... Src |-> bool ... </typeEnv>
        <compiled> ListItem(Cur => (Cur receiveValue(Src, Dst))) ... </compiled>
    rule <k> sendValues(Src, Dst) => . ... </k>
        <typeEnv> ... Src |-> table(.Vars) _ ... </typeEnv>
        <compiled>
            ListItem(S => S (
                for (uint genVar(!I) = 0; genVar(!I) < (Src.length); genVar(!I)++) {
                    receiveValue(Src[genVar(!I)], Dst)
                }
                delete Src;
            ))
            ...
        </compiled>

    rule sendValues(source(.List), _) => .
    rule <k> sendValues(source(ListItem(Val) Rest), Dst) => sendValues(source(Rest), Dst) ... </k>
        <compiled> ListItem(S => (S receiveValue(Val, Dst))) ... </compiled>
    rule sendValues(sourceSelect(Src, Sel), Dst) => sendValues(Src, guardSelect(Sel, Dst))

    rule sendValues(sourceFilter(Src, Q, F, Args), Dst) => sendValues(Src, filterInto(Q, F, Args, Dst))

    rule [[ receiveValue(Src, Dst) => (Dst = Dst + Src; Src = 0;) ]]
        <typeEnv> ... Dst |-> nat ... </typeEnv>

    rule [[ receiveValue(Src, Dst) => (Dst = Dst || Src; Src = false;) ]]
        <typeEnv> ... Dst |-> bool ... </typeEnv>

    rule [[ receiveValue(Src, Dst) => Dst.push(Src); ]]
        <typeEnv> ... Dst |-> table(.Vars) _ </typeEnv>

    rule [[ receiveValue(Src, Dst) => (
                Dst.underlying_map[Src.key] = Src.value;
                Dst.keys.push(Src.key);
        )]]
        <typeEnv> ... Dst |-> map _ => _ ... </typeEnv>

    rule receiveValue(Src, guardSelect(Sel, Dst))
         => if (Src == Sel) { receiveValue(Src, Dst) }

    rule receiveValue(Src, filterInto(Q, F, Args, Dst)) =>
            if (buildCall(F, Args, Src)) {
                receiveValue(Src, Dst)
            }

    syntax Expr ::= buildCall(Var, Locateds, Expr) [function]
                  | buildExpr(Located) [function]

    rule buildCall(F, Args, LastArg) => F(appendExpr(buildExprs(Args), LastArg))

    // TODO: Finish this
    rule buildExpr(X:Var) => X

    syntax Exprs ::= buildExprs(Locateds) [function]
                   | appendExpr(Exprs, Expr) [function, functional]

    rule buildExprs(.Locateds) => .Exprs
    rule buildExprs(L:Located, Ls) => buildExpr(L), buildExprs(Ls)

    rule appendExpr(.Exprs, E) => E
    rule appendExpr((E:Expr, Es), E') => E, appendExpr(Es, E')

    syntax KItem ::= flowNew(Locator, Var, Locators, Locators) [strict(1,3,4)]

    // TODO: This isn't quite right, because it won't handle a list correctly.
    /* rule <k> A --> new T(Locs) --> B => flowNew( */
    /*                                             A, /1* locate(A, baseTypeOf(lastVDef(getConstructorArgs(BaseT)))), *1/ */
    /*                                             T, */
    /*                                             locateEach(Locs, tailVDefs(getConstructorArgs(BaseT))), */
    /*                                             B) ... </k> */
    /*     <types> ... T |-> type T is _ BaseT ... </types> */
    // TODO: Finish getConstructoArgs

    /* rule <k> flowNew(X:Var, T, Args:Vars, Y:Var) */

    syntax Locator ::= locate(Locator)

    rule <k> locate(V:Int) => genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> nat ... </typeEnv>
        <compiled> ListItem(Ss => Ss (uint genVar(!I) = V;)) ... </compiled>
        <tempVars> ... .Set => SetItem(genVar(!I)) ... </tempVars>

    rule <k> locate(B:Bool) => genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> bool ... </typeEnv>
        <compiled> ListItem(S => S (bool genVar(!I) = B;)) ... </compiled>
        <tempVars> ... .Set => SetItem(genVar(!I)) ... </tempVars>

    rule <k> locate([ _ T ; Locs ]) => locateEach(Locs, .List) ... </k>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax KItem ::= locateEach(Locators, List)
    rule locateEach(.Locators, Res) => source(Res)
    rule locateEach((L:Locator, Ls), Res) => locate(L) ~> locateEach(Ls, Res)
    rule Y:Located ~> locateEach(Locs, Res) => locateEach(Locs, Res ListItem(Y))

    rule <k> locate(record(Keys) { Members }) => locateRecordFields(genVar(!I), Members) ~> genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> record(Keys) { membersToDefs(Members) } ... </typeEnv>
        <compiled> ListItem(Ss:SolStmts => Ss (baseTypeToSolType(record(Keys) { membersToDefs(Members) }) genVar(!I);)) ... </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(record(Keys) { membersToDefs(Members) }), record(Keys) { membersToDefs(Members) })) </structs>

    syntax KItem ::= locateRecordFields(Var, RecordMembers)
                   | setField(Var, Var)
    rule locateRecordFields(_, .RecordMembers) => .
    rule locateRecordFields(X, ((F : _ |-> V), Rest:RecordMembers))
         => locate(V) ~> setField(X, F) ~> locateRecordFields(X, Rest)

    rule <k> Y:Var ~> setField(X, F) => . ... </k>
        <compiled> ListItem(Ss => Ss (X.F = Y;)) ... </compiled>

    rule locate(X:Var) => X
    rule locate(demote(L)) => locate(L)

    context locate(copy(HOLE => locate(copy(HOLE))))
    rule <k> locate(copy(X:Var)) => X ... </k>
        // TODO: Does this actually copy everything?
        <compiled> ListItem(Ss => Ss (baseTypeToSolType(T) genVar(!I) = X;)) ... </compiled>
        <typeEnv> ... (X |-> T) (.Map => genVar(!I) |-> T) ... </typeEnv>

    rule <k> locate(var X : T) => X ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <compiled> ListItem(Ss:SolStmts => Ss (baseTypeToSolType(T) X;)) ... </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax KItem ::= locateSelector(Locator, Locator) [seqstrict]
    rule locate(L[K]) => locateSelector(locate(L), locate(K))
    rule locateSelector(L, K) => sourceSelect(L, K)

    syntax KItem ::= locateFilter(Locator, TypeQuant, Var, Locators) [seqstrict(4,1)]
    // TODO: Need to check that the args get evaluated correctly **BEFORE** the filtered collections
    rule locate(L[Q such that F(Args)]) => locateFilter(locate(L), Q, F, Args)
    rule locateFilter(L, Q, F, Args) => sourceFilter(L, Q, F, Args)

    syntax Var ::= nameOf(BaseType) [function, functional]
    rule nameOf(X:Var) => X
    rule nameOf(record(Keys) { Fields }) => String2Id("record_" +String varsName(Keys) +String "_" +String genName(Fields))
    rule nameOf(table (_) T) => String2Id("table_" +String typeToString(T))

    syntax String ::= typeToString(Type) [function, functional]
                    | baseTypeToString(BaseType) [function, functional]
                    | quantToString(TypeQuant) [function, functional]
                    | varsName(Vars) [function, functional]
                    | genName(VarDefs) [function, functional]
    rule genName(.VarDefs) => ""
    rule genName(X : T, Fields) => baseTypeToString(X) +String "__" +String typeToString(T) +String genName(Fields)

    rule varsName(.Vars) => ""
    rule varsName(X:Var, Xs) => baseTypeToString(X) +String "_" +String varsName(Xs)

    rule quantToString(any) => "any"
    rule quantToString(one) => "one"
    rule quantToString(nonempty) => "nonempty"
    rule quantToString(empty) => "empty"
    rule quantToString(every) => "every"

    rule typeToString(Q T) => quantToString(Q) +String baseTypeToString(T)
    rule typeToString(T:BaseType) => baseTypeToString(T)

    rule baseTypeToString(nat) => "nat"
    rule baseTypeToString(string) => "string"
    rule baseTypeToString(bool) => "bool"
    rule baseTypeToString(address) => "address"
    // NOTE: Kind of annoying I need to define this for every special variable I add. Avoidable?
    rule baseTypeToString(key) => "key"
    rule baseTypeToString(value) => "value"
    rule baseTypeToString(X:Id) => Id2String(X)
    rule baseTypeToString(X.Y) => baseTypeToString(X) +String "___" +String baseTypeToString(Y)
    rule baseTypeToString(record(Keys) { Fields }) => "record_" +String varsName(Keys) +String "_" +String genName(Fields)
    /* rule baseTypeToString(map T1 => T2) => "map_" +String typeToString(T1) +String "_to_" +String typeToString(T2) */
    rule baseTypeToString(table(Keys) ElemT) => "table_" +String varsName(Keys) +String "_" +String typeToString(ElemT)

    syntax Id ::= genVar(Int) [function, functional]
    rule genVar(I) => String2Id("v" +String Int2String(I))

    syntax SolType ::= typeToSolType(Type) [function, functional]
                     | baseTypeToSolType(BaseType) [function, functional]

    rule typeToSolType(_:TypeQuant T) => baseTypeToSolType(T)
    rule typeToSolType(T:BaseType) => baseTypeToSolType(T)

    rule baseTypeToSolType(bool) => bool
    rule baseTypeToSolType(nat) => uint
    rule baseTypeToSolType(string) => string
    rule baseTypeToSolType(address) => address
    rule [[ baseTypeToSolType(X:Var) => SolT ]]
        <typeEncoding> ... X |-> SolT ... </typeEncoding>
    rule baseTypeToSolType(record(Keys) { Fields }) => nameOf(record(Keys) { Fields })
    rule baseTypeToSolType(table(Keys) T) => nameOf(table(Keys) T)

    syntax SolType ::= encodeType(Var, BaseType) [function, functional]
    rule encodeType(_, nat) => baseTypeToSolType(nat)
    rule encodeType(_, string) => baseTypeToSolType(string)
    rule encodeType(_, address) => baseTypeToSolType(address)
    rule encodeType(_, bool) => baseTypeToSolType(bool)
    rule encodeType(_, map T1 => T2) => baseTypeToSolType(map T1 => T2)
    rule encodeType(T, record(_) { _ }) => T

    syntax SolVarDefs ::= encodeFields(VarDefs) [function, functional]
    rule encodeFields(.VarDefs) => .SolVarDefs
    rule encodeFields(X : T, Fields) => (typeToSolType(T) X;) encodeFields(Fields)
endmodule

