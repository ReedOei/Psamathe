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
                  | Expr "<=" Expr
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

    syntax SourceList ::= source(Type, List)
                        | sourceSelect(Located, Located)
                        | sourceFilter(Located, TypeQuant, Var, Locateds)
    syntax Located ::= Var
                     | SourceList
                     | intConst(Int)
                     | boolConst(Bool)
                     | guardSelect(Located, Located)
                     | filterInto(TypeQuant, Var, Locateds, Located)
                     | fieldOf(Located, Var)
                     | fromField(Var, Located)
                     | receiveInFieldFrom(BaseType, Var, Expr, Expr)
                     | receiveFrom(BaseType, Expr, Expr)
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
        <types> ... .Map => T |-> typeDef(modifiersToSet(Ms), BaseT) ... </types>
        <typeEncoding> ... .Map => T |-> encodeType(T, BaseT) ... </typeEncoding>
        <structs> Structs => union(Structs, defineStructs(T, BaseT)) </structs>

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
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

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

    syntax KItem ::= "appendStmts"
    rule <k> New:SolStmts ~> appendStmts => . ... </k>
        <compiled> ListItem(S => (S New)) ... </compiled>

    syntax KItem ::= lookupValues(Located, Located)

    rule flow(Src, Dst) => lookupValues(Src, Dst) ~> appendStmts

    rule <k> lookupValues(Src, Dst) => receiveValue(Src, Src, Dst) ... </k>
        <typeEnv> ... Src |-> nat ... </typeEnv>
    rule <k> lookupValues(Src, Dst) => receiveValue(Src, Src, Dst) ... </k>
        <typeEnv> ... Src |-> bool ... </typeEnv>
    rule lookupValues(intConst(V), Dst) => receiveValue(V, V, Dst)
    rule lookupValues(boolConst(B), Dst) => receiveValue(B, B, Dst)

    rule <k> lookupValues(Src, Dst) => receiveValue(Src[genVar(!I)], Src[genVar(!I)], Dst) ~> lookupValues(Src, Dst) ... </k>
        <typeEnv> ... Src |-> table(.Vars) _ ... </typeEnv>
    rule <k> Body:SolStmts ~> lookupValues(Src, _) =>
                for (uint genVar(!I) = 0; genVar(!I) < (Src.length); genVar(!I)++) {
                    Body
                    // TODO: Need to delete the selected values
                } ... </k>
        <typeEnv> ... Src |-> table(.Vars) _ ... </typeEnv>

    rule <k> lookupValues(Src, Dst) =>
                receiveValue(buildExpr(Src).underlying_map[buildExpr(Src).keys[genVar(!I)]],
                             buildExpr(Src).underlying_map[buildExpr(Src).keys[genVar(!I)]],
                             Dst) ~> lookupValues(Src, Dst) ... </k>
        <typeEnv> ... Src |-> map _ => _ ... </typeEnv>
    rule <k> Body:SolStmts ~> lookupValues(Src, _) =>
            for (uint genVar(!I) = 0; genVar(!I) < (buildExpr(Src).keys.length); genVar(!I)++) {
                Body
                // TODO: Need to delete the selected values
            } ... </k>
        <typeEnv> ... Src |-> map _ => _ ... </typeEnv>

    rule <k> lookupValues(sourceSelect(Src, Sel), Dst) => receiveValue(buildExpr(Src).underlying_map[Sel].value, buildExpr(Src).underlying_map[Sel].value, Dst) ... </k>
        <typeEnv> ... (Src |-> map _ K => _) (Sel |-> K) ... </typeEnv>

    rule lookupValues(source(_, .List), _) => .SolStmts
    rule lookupValues(source(T, ListItem(Val) Rest), Dst)
        => receiveValue(buildExpr(Val), buildExpr(Val), Dst) ~> lookupValues(source(T, Rest), Dst)
    rule Ss:SolStmts ~> lookupValues(source(T, Vals), Dst) => Ss ~> appendStmts ~> lookupValues(source(T, Vals), Dst)

    rule lookupValues(sourceSelect(Src, Sel), Dst) => lookupValues(Src, guardSelect(Sel, Dst))
        requires selectCompat(demoteBaseType(typeof(Src)), demoteBaseType(typeof(Sel)))

    rule lookupValues(sourceFilter(Src, Q, F, Args), Dst) => lookupValues(Src, filterInto(Q, F, Args, Dst))

    rule lookupValues(fieldOf(Src, X), Dst) => lookupValues(Src, fromField(X, Dst))

    syntax Bool ::= selectCompat(BaseType, BaseType) [function]
    rule selectCompat(X, X) => true
    rule selectCompat(table(_) _ T, T) => true
    rule selectCompat(_, _) => false [owise]

    syntax BaseType ::= typeof(Located) [function]
    // TODO: Need to make sure these are right
    rule typeof(source(T, _)) => list T
    rule [[ typeof(X) => T ]]
        <typeEnv> ... X |-> T ... </typeEnv>
    rule typeof(fieldOf(Dst, X)) => coerceMaybeType(lookupField(typeof(Dst), X))
    // TODO: Reduce duplication of typeof(L)
    rule typeof(sourceSelect(L, K)) => #if typeof(K) in keyTypes(typeof(L)) #then valueType(typeof(L)) #else typeof(L) #fi
    rule typeof(intConst(_)) => nat
    rule typeof(boolConst(_)) => bool

    syntax Set ::= keyTypes(BaseType) [function]
    rule keyTypes(nat) => SetItem(nat)
    rule keyTypes(bool) => SetItem(bool)
    rule keyTypes(string) => SetItem(string)
    rule keyTypes(address) => SetItem(address)
    rule keyTypes(record(Keys) { Fields }) => lookupTypes(Fields, Keys) SetItem(record(Keys) { Fields })
    rule keyTypes(table(Keys) Q T) => SetItem(table(Keys) Q T) keyTypes(T)
    rule [[ keyTypes(T) => SetItem(T) keyTypes(demoteBaseType(T))  ]]
        <types> ... T |-> _ ... </types>

    syntax BaseType ::= valueType(BaseType) [function]
    rule valueType(map _ => _ V) => V
    rule valueType(record(Keys) { Fields }) => coerceMaybeType(makeValueType(withoutKeys(Fields, Keys)))

    syntax MaybeType ::= makeValueType(VarDefs) [function]
    rule makeValueType(.VarDefs) => none
    rule makeValueType(_ : _ T) => some(T)
    rule makeValueType(X : T1, Y : T2, Rest) => some(record(.Vars) { X : T1, Y : T2, Rest })

    syntax KItem ::= receiveValue(Expr, Expr, Located)
                   | receiveExpr(BaseType, Expr, Expr, Expr)

    rule <k> receiveValue(Orig, Src, Dst) => receiveExpr(demoteBaseType(T), Orig, Src, buildExpr(Dst)) ... </k>
        <typeEnv> ... Dst |-> T ... </typeEnv>
        requires isFungible(T)

    rule <k> receiveValue(Orig, Src, Dst) => receiveExpr(demoteBaseType(T), Orig, Src, buildExpr(Dst)) ... </k>
        <typeEnv> ... Dst |-> T ... </typeEnv>
        requires demoteBaseType(T) ==K bool

    rule <k> receiveValue(Orig, Src, Dst) => receiveExpr(demoteBaseType(T), Orig, Src, buildExpr(Dst)) ... </k>
        <typeEnv> ... Dst |-> T ... </typeEnv>
        requires (table(.Vars) _) :=K demoteBaseType(T)

    rule <k> receiveValue(Orig, Src, Dst) => receiveExpr(map K => V, Orig, Src, buildExpr(Dst)) ... </k>
        <typeEnv> ... Dst |-> map K => V ... </typeEnv>

    rule receiveValue(Orig, Src, guardSelect(Sel, Dst))
         => receiveValue(Orig, selectedPart(Src, Sel), Dst) ~> receiveValue(Orig, Src, guardSelect(Sel, Dst))
    rule Body:SolStmts ~> receiveValue(_, Src, guardSelect(Sel, _))
         => if (containedIn(Src, Sel)) {
                Body
            }

    rule receiveValue(Orig, Src, filterInto(Q, F, Args, Dst)) =>
            receiveValue(Orig, Src, Dst) ~> receiveValue(Orig, Src, filterInto(Q, F, Args, Dst))
    rule Body:SolStmts ~> receiveValue(_, Src, filterInto(Q, F, Args, _)) =>
            if (buildCall(F, Args, Src)) {
                Body
            }

    rule receiveValue(Orig, Src, fieldOf(Dst, X))
        => lookupValues(Dst, receiveInFieldFrom(coerceMaybeType(lookupField(typeof(Dst), X)), X, Orig, Src))
    rule receiveValue(_, Dst, receiveInFieldFrom(T, X, Orig, Src)) => receiveExpr(T, Orig, Src, Dst.X)
    rule receiveValue(Orig, Src, fromField(X, Dst)) => receiveValue(Orig.X, Src.X, Dst)

    rule receiveValue(Orig, Src, sourceSelect(Dst, DstSel))
        => lookupValues(sourceSelect(Dst, DstSel), receiveFrom(typeof(sourceSelect(Dst, DstSel)), Orig, Src))

    rule receiveValue(_, Dst, receiveFrom(T, Orig, Src)) => receiveExpr(T, Orig, Src, Dst)

    rule receiveExpr(T, Orig, Src, Dst)
        => Dst = Dst + Src;
           #if _:Int :=K Orig #then .SolStmts #else Orig = Orig - Src; #fi
        requires isFungible(T) andBool demoteBaseType(T) ==K nat
    rule receiveExpr(bool, Orig, Src, Dst)
        => Dst = Dst || Src;
           #if _:Bool :=K Orig #then .SolStmts #else Orig = false; #fi
    rule receiveExpr(table(.Vars) _, Orig, Src, Dst) => Dst.push(Src);
    rule receiveExpr(map _ => _, Orig, Src, Dst) =>
            Dst.underlying_map[Src.key] = Src.value;
            Dst.keys.push(Src.key);
    rule receiveExpr(T, Orig, Src, Dst) => Src = Dst; delete Orig;
        requires singletonType(T)

    syntax Bool ::= singletonType(BaseType) [function]
    rule singletonType(address) => true
    rule singletonType(string) => true
    rule singletonType(record(_) { _ }) => true
    rule [[ singletonType(T) => notBool(fungible in Ms) ]]
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
    rule singletonType(_) => false [owise]

    syntax Expr ::= buildCall(Var, Locateds, Expr) [function]
                  | buildExpr(Located) [function]

    rule buildCall(F, Args, LastArg) => F(appendExpr(buildExprs(Args), LastArg))

    // TODO: Finish this
    rule buildExpr(X:Var) => X
    rule buildExpr(intConst(V)) => V
    rule buildExpr(boolConst(B)) => B

    syntax Expr ::= containedIn(Expr, Located) [function]
    rule containedIn(_, source(_, .List)) => false
    rule containedIn(Src, source(_, ListItem(Elem))) => Src == buildExpr(Elem)
    rule containedIn(Src, source(T, ListItem(E1) ListItem(E2) Rest)) => (Src == buildExpr(E1)) || containedIn(Src, source(T, ListItem(E2) Rest))
    rule [[ containedIn(X, Y) => buildExpr(Y) <= X ]]
        <typeEnv> ... Y |-> T ... </typeEnv>
        requires isFungible(T)
    rule containedIn(X, Y) => X == buildExpr(Y) [owise]

    syntax Expr ::= selectedPart(Expr, Located) [function]
    rule selectedPart(X, source(_, _)) => X
    rule [[ selectedPart(_, Y) => buildExpr(Y) ]]
        <typeEnv> ... Y |-> T ... </typeEnv>
        requires isFungible(T)
    rule selectedPart(X, _) => X [owise]

    syntax Exprs ::= buildExprs(Locateds) [function]
                   | appendExpr(Exprs, Expr) [function, functional]

    rule buildExprs(.Locateds) => .Exprs
    rule buildExprs(L:Located, Ls) => buildExpr(L), buildExprs(Ls)

    rule appendExpr(.Exprs, E) => E
    rule appendExpr((E:Expr, Es), E') => E, appendExpr(Es, E')

    syntax KItem ::= flowNew(Locator, Var, Locators, Locators) [seqstrict]

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

    rule locate(V:Int) => intConst(V)
    rule locate(B:Bool) => boolConst(B)

    rule <k> locate([ Q T ; Locs ]) => locateEach(Q T, Locs, .List) ... </k>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax KItem ::= locateEach(Type, Locators, List)
    rule locateEach(T, .Locators, Res) => source(T, Res)
    rule locateEach(T, (L:Locator, Ls), Res) => locate(L) ~> locateEach(T, Ls, Res)
    rule Y:Located ~> locateEach(T, Locs, Res) => locateEach(T, Locs, Res ListItem(Y))

    rule <k> locate(record(Keys) { Members }) => locateRecordFields(genVar(!I), Members) ~> genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> record(Keys) { membersToDefs(Members) } ... </typeEnv>
        <compiled> ListItem(Ss:SolStmts => Ss (baseTypeToSolType(record(Keys) { membersToDefs(Members) }) genVar(!I);)) ... </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(record(Keys) { membersToDefs(Members) }), record(Keys) { membersToDefs(Members) })) </structs>

    syntax KItem ::= locateRecordFields(Var, RecordMembers)
                   | setField(Var, Var)
    rule locateRecordFields(_, .RecordMembers) => .
    rule locateRecordFields(X, ((F : _ |-> V), Rest:RecordMembers))
         => locate(V) ~> setField(X, F) ~> locateRecordFields(X, Rest)

    rule <k> L:Located ~> setField(X, F) => . ... </k>
        <compiled> ListItem(Ss => Ss (X.F = buildExpr(L);)) ... </compiled>

    rule locate(X:Var) => X

    syntax Locator ::= locateField(Locator, Var) [seqstrict(1)]
    rule locate(L.X) => locateField(locate(L), X)
    rule locateField(L, X) => fieldOf(L, X)

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

