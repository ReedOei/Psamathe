requires "pure-flow-common.k"

module SOLIDITY-SYNTAX
    imports DOMAINS
    imports VARS

    syntax DataLoc ::= "memory" | "calldata" | "storage"
    syntax SolVar ::= SolType DataLoc Var
                    | SolType Var
    syntax SolArgs ::= List{SolVar, ","}

    syntax SolVarDef ::= SolVar ";"
    syntax SolVarDefs ::= List{SolVarDef, ""}

    syntax Access ::= Var
                    | Expr "." Var [klabel(qualified)]
    syntax Expr ::= Bool | Int | Access | Hex | String
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
                     | "for" "(" SolStmt Expr ";" Expr ")" "{" SolStmts "}"
                     | "try" Expr "returns" "(" SolArgs ")" "{" SolStmts "}" "catch" "{" SolStmts "}"
                     | "if" "(" Expr ")" "{" SolStmts "}"
    syntax SolStmts ::= ".SolStmts"
                      | SolStmt
                      | SolStmts SolStmts [assoc, right]
                      // List{SolStmt, ""} [klabel(stmts)]

    syntax SolType ::= Var
                     | SolType "[]"
                     | "mapping" "(" SolType "=>" SolType ")"

    syntax Struct ::= "struct" Var "{" SolVarDefs "}"
    syntax Visibility ::= "public" | "private" | "public" | "external"
    syntax Function ::= "function" Var "(" SolArgs ")" Visibility "returns" "(" SolArgs ")" "{" SolStmts "}"
    syntax Constructor ::= "constructor" "(" SolArgs ")" "{" SolStmts "}"

    syntax SolDecl ::= Struct | Function | Constructor | SolVarDef

    syntax SolDecls ::= List{SolDecl, ""}
    syntax SolVerNum ::= "^0.7.5"
    syntax SolVer ::= "pragma" "solidity" SolVerNum ";"
    syntax Contract ::= SolVer "contract" Var "{" SolDecls "}"

    syntax Set ::= varsOfExpr(Expr) [function, functional]
                 | varsOfEachExpr(Exprs) [function, functional]
                 | varsOfSolStmt(SolStmt) [function, functional]
                 | varsOfSolStmts(SolStmts) [function, functional]
                 | varsOfFields(SolFields) [function, functional]

    rule varsOfExpr(_:Bool) => .Set
    rule varsOfExpr(_:Int) => .Set
    rule varsOfExpr(_:String) => .Set
    rule varsOfExpr(_:Hex) => .Set
    rule varsOfExpr(X:Var) => SetItem(X)
    rule varsOfExpr(E._) => varsOfExpr(E)
    rule varsOfExpr(E++) => varsOfExpr(E)
    // TODO: If we ever call functions from something more complicated than f(x) (e.g., a[i].f(x)), we'll need to amend this
    rule varsOfExpr((_:Expr(Args)):Expr) => varsOfEachExpr(Args)
    rule varsOfExpr(_({ Fields })) => varsOfFields(Fields)
    rule varsOfExpr(A + B) => varsOfExpr(A) varsOfExpr(B)
    rule varsOfExpr(A - B) => varsOfExpr(A) varsOfExpr(B)
    rule varsOfExpr(A || B) => varsOfExpr(A) varsOfExpr(B)
    rule varsOfExpr(A < B) => varsOfExpr(A) varsOfExpr(B)
    rule varsOfExpr(A <= B) => varsOfExpr(A) varsOfExpr(B)
    rule varsOfExpr(A == B) => varsOfExpr(A) varsOfExpr(B)

    rule varsOfEachExpr(.Exprs) => .Set
    rule varsOfEachExpr(E, Es) => varsOfExpr(E) varsOfEachExpr(Es)

    rule varsOfFields(.SolFields) => .Set
    rule varsOfFields(_ : E, Fields) => varsOfExpr(E) varsOfFields(Fields)

    rule varsOfSolStmt(E;) => varsOfExpr(E)
    rule varsOfSolStmt(E1 = E2;) => varsOfExpr(E1) varsOfExpr(E2)
    rule varsOfSolStmt(_:SolVarDef) => .Set
    rule varsOfSolStmt(_ _ = E;) => varsOfExpr(E)
    rule varsOfSolStmt(_ _ _ = E;) => varsOfExpr(E)
    rule varsOfSolStmt(delete E;) => varsOfExpr(E)
    rule varsOfSolStmt(for(S Cond ; Inc) { Body }) => varsOfSolStmt(S) varsOfExpr(Inc) varsOfExpr(Cond) varsOfSolStmts(Body)
    rule varsOfSolStmt(if (Cond) { Body }) => varsOfSolStmts(Body) varsOfExpr(Cond)

    rule varsOfSolStmts(.SolStmts) => .Set
    rule varsOfSolStmts(S) => varsOfSolStmt(S)
    rule varsOfSolStmts(.SolStmts S) => varsOfSolStmts(S)
    rule varsOfSolStmts(S1:SolStmt S2:SolStmts) => varsOfSolStmt(S1) varsOfSolStmts(S2)
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
                     | addrConst(Hex)
                     | boolConst(Bool)
                     | strConst(String)
                     | guardSelect(Located, Located)
                     | filterInto(TypeQuant, Var, Locateds, Located)
                     | fieldOf(Located, Var)
                     | fromField(Var, Located)
                     | receiveInFieldFrom(BaseType, Var, Expr, Expr)
                     | receiveFrom(BaseType, Expr, Expr)
                     | construct(Var, Locateds, Located)
                     | callTransformer(Var, Locateds, Located)
    syntax Locateds ::= List{Located, ","} [klabel(locators)]
                      | Vars
    syntax Locators ::= Locateds
    syntax Locator ::= Located
    syntax KResult ::= Located
                     | Vars
                     | Locateds

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

    rule D:Decl => translateDecl(D) [structural]

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

    rule <k> run(Stmts) => Stmts ~> done ... </k>
        <compiled> .List => ListItem(.SolStmts) ... </compiled>

    rule <k> done
             =>
             pragma solidity ^0.7.5;
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
                   | defFunc(Var, VarDefs, Var, Type)

    rule <k> translateDecl(transformer F(Args) -> X : Q T { Body })
            => setupArgs(X : empty T, Args) ~>
               Body ~>
               defFunc(F, Args, X, Q T) ... </k>
        <functions> ... .Map => F |-> transformer(X : Q T, Args, Body) ... </functions>
        <compiled> .List => ListItem(.SolStmts) ... </compiled>

    rule setupArgs(.VarDefs) => .
    rule <k> setupArgs(X : _ T, Rest) => setupArgs(Rest) ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax SolArgs ::= varDefsToSolArgs(VarDefs) [function, functional]
    rule varDefsToSolArgs(.VarDefs) => .SolArgs
    rule varDefsToSolArgs(X : T, Rest) => varDefToSolVar(X : T), varDefsToSolArgs(Rest)

    syntax Bool ::= isPrimitive(SolType) [function, functional]
    rule isPrimitive(T) => T ==K uint orBool T ==K bool orBool T ==K address

    syntax SolVar ::= varDefToSolVar(VarDef) [function]
    rule varDefToSolVar(X : _ T) =>
            #if isPrimitive(baseTypeToSolType(T)) #then
                baseTypeToSolType(T) X
            #else
                baseTypeToSolType(T) memory X
            #fi

    rule <k> defFunc(F, Args, RetVar, RetType) => . ... </k>
        <solFunctions>
            ...
            .Map => F |->
            function F(varDefsToSolArgs(Args)) public returns (varDefToSolVar(RetVar : RetType)) {
                Body
            }
            ...
        </solFunctions>
        <typeEnv> _ => .Map </typeEnv>
        <compiled> ListItem(Body) => .List ... </compiled>

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

    syntax KItem ::= "tryCatch"
    rule <k> try { S1 } catch { S2 } => S1 ~> newScope ~> S2 ~> /ryCatch ... </k>
        <compiled> .List => ListItem(.SolStmts) ... </compiled>

    // TODO: We only want to pack the vars that we're actually going to end up using
    rule <k> tryCatch => makeClosure(TryBlock, CatchBlock, removeAll(Env, keys(Env) -Set varsOfSolStmts(TryBlock))) ... </k>
        <typeEnv> Env </typeEnv>
        <compiled> ListItem(CatchBlock) ListItem(TryBlock) => .List ... </compiled>

    syntax KItem ::= makeClosure(SolStmts, SolStmts, Map)
    rule <k> makeClosure(TryBlock, CatchBlock, Env) => . ... </k>
        <compiled>
            ListItem(S => (S
                (try this.(closureName(!I))(envToExprs(keys_list(Env))) returns (outNames(envToArgs(keys_list(Env), Env))) {
                    unpackScope(Env)
                } catch {
                    CatchBlock
                })))
            ...
        </compiled>
        <solFunctions>
            ...
            .Map => closureName(!I) |->
            function closureName(!I)(envToArgs(keys_list(Env), Env))
                public returns (outNames(envToArgs(keys_list(Env), Env))) {
                TryBlock
                packScope(Env)
            }
            ...
        </solFunctions>

    syntax SolArgs ::= outNames(SolArgs) [function, functional]
    rule outNames(.SolArgs) => .SolArgs
    rule outNames(T X, Rest) => T outName(X), outNames(Rest)
    rule outNames(T DL X, Rest) => T DL outName(X), outNames(Rest)

    syntax Var ::= outName(Var) [function, functional]
    rule outName(X) => String2Id(Id2String(X) +String "_out")

    syntax Exprs ::= envToExprs(List) [function, functional]
    rule envToExprs(.List) => .Exprs
    rule envToExprs(ListItem(X) Rest) => X, envToExprs(Rest)

    syntax SolArgs ::= envToArgs(List, Map) [function, functional]
    rule envToArgs(.List, _) => .SolArgs
    rule envToArgs(ListItem(X) Rest, (X |-> T) M) => varDefToSolVar(X : any T), envToArgs(Rest, M)

    syntax SolVarDefs ::= mapToSolVars(Map) [function, functional]
    rule mapToSolVars(.Map) => .SolVarDefs
    rule mapToSolVars((X |-> T) M) => baseTypeToSolType(T) X; mapToSolVars(M)

    syntax SolStmts ::= packScope(Map) [function, functional]
    rule packScope(.Map) => .SolStmts
    rule packScope((Y |-> _) Env) => outName(Y) = Y; packScope(Env)

    syntax SolStmts ::= unpackScope(Map) [function, functional]
    rule unpackScope(.Map) => .SolStmts
    rule unpackScope((Y |-> _) Env) => Y = outName(Y); unpackScope(Env)

    syntax Var ::= closureName(Int) [function, functional]
    rule closureName(I) => String2Id("closure_" +String Int2String(I))

    syntax KItem ::= flow(Locator, Locator) [seqstrict]
    rule A --> B => flow(locate(A), locate(B))
    rule flow(Src, Dst) => lookupValues(Src, Dst) ~> appendStmts

    syntax KItem ::= "appendStmts"
    rule <k> New:SolStmts ~> appendStmts => . ... </k>
        <compiled> ListItem(S => (S New)) ... </compiled>

    syntax KItem ::= lookupValues(Located, Located)

    rule <k> lookupValues(Src, Dst) => receiveValue(Src, Src, Dst) ... </k>
        <typeEnv> ... Src |-> nat ... </typeEnv>
    rule <k> lookupValues(Src, Dst) => receiveValue(Src, Src, Dst) ... </k>
        <typeEnv> ... Src |-> bool ... </typeEnv>
    rule lookupValues(intConst(V), Dst) => receiveValue(V, V, Dst)
    rule lookupValues(addrConst(Addr), Dst) => receiveValue(Addr, Addr, Dst)
    rule lookupValues(strConst(S), Dst) => receiveValue(S, S, Dst)
    rule lookupValues(boolConst(B), Dst) => receiveValue(B, B, Dst)

    syntax KItem ::= freshVar(Int)

    rule <k> lookupValues(Src, Dst) => receiveValue(Src[genVar(!I)], Src[genVar(!I)], Dst) ~> freshVar(!I) ~> lookupValues(Src, Dst) ... </k>
        <typeEnv> ... Src |-> table(.Vars) _ ... </typeEnv>
    rule <k> Body:SolStmts ~> freshVar(I) ~> lookupValues(Src, _) =>
                for (uint genVar(I) = 0; genVar(I) < (Src.length); genVar(I)++) {
                    Body
                    // TODO: Need to delete the selected values
                } ... </k>
        <typeEnv> ... Src |-> table(.Vars) _ ... </typeEnv>

    rule <k> lookupValues(Src, Dst) =>
                receiveValue(buildExpr(Src).underlying_map[buildExpr(Src).keys[genVar(!I)]],
                             buildExpr(Src).underlying_map[buildExpr(Src).keys[genVar(!I)]],
                             Dst) ~> freshVar(!I) ~> lookupValues(Src, Dst) ... </k>
        <typeEnv> ... Src |-> map _ => _ ... </typeEnv>
    rule <k> Body:SolStmts ~> freshVar(I) ~> lookupValues(Src, _) =>
            for (uint genVar(I) = 0; genVar(I) < (buildExpr(Src).keys.length); genVar(I)++) {
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
    rule typeof(sourceSelect(L, K)) =>
        #fun(LT => #if typeof(K) in keyTypes(LT) #then valueType(LT) #else LT #fi)(typeof(L))
    rule typeof(intConst(_)) => nat
    rule typeof(boolConst(_)) => bool
    rule typeof(strConst(_)) => string
    rule typeof(addrConst(_)) => address

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

    rule <k> receiveValue(Orig, Src, Dst) => receiveExpr(T, Orig, Src, buildExpr(Dst)) ... </k>
        <typeEnv> ... Dst |-> T ... </typeEnv>
        requires singletonType(T)

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

    rule <k> receiveValue(Orig, Src, construct(T, _, Dst))
            => receiveValue(Orig, Src, Dst) ... </k>
        <types> ... T |-> typeDef(_, BaseT) ... </types>
        requires BaseT in (SetItem(nat) SetItem(bool) SetItem(string) SetItem(address))
    rule <k> receiveValue(Orig, Src, construct(T, Args, Dst))
            => receiveValue(Orig, buildCall(T, Args, Src), Dst) ... </k>
        <types> ... T |-> typeDef(_, record(_) { _ }) ... </types>

    rule receiveValue(Orig, Src, callTransformer(F, Args, Dst)) => receiveValue(Orig, buildCall(F, Args, Src), Dst)

    rule receiveExpr(T, Orig, Src, Dst)
        => #if _:Int :=K Orig #then
            Dst = Dst + Src;
           #else
            Dst = Dst + Src;
            Orig = Orig - Src;
           #fi
        requires isFungible(T) andBool demoteBaseType(T) ==K nat
    rule receiveExpr(bool, Orig, Src, Dst)
        => #if _:Bool :=K Orig #then
            Dst = Dst || Src;
           #else
            Dst = Dst || Src;
            Orig = false;
           #fi
    rule receiveExpr(table(.Vars) _, Orig, Src, Dst) => Dst.push(Src);
    rule receiveExpr(map _ => _, Orig, Src, Dst) =>
            Dst.underlying_map[Src.key] = Src.value;
            Dst.keys.push(Src.key);
    rule receiveExpr(T, Orig, Src, Dst) => Dst = Src; delete Orig;
        requires singletonType(T)

    syntax Bool ::= singletonType(BaseType) [function]
    rule singletonType(address) => true
    rule singletonType(string) => true
    rule singletonType(record(_) { _ }) => true
    rule [[ singletonType(T) => notBool(fungible in Ms) ]]
        <types> ... T |-> typeDef(Ms, _) ... </types>
    rule singletonType(_) => false [owise]

    syntax Expr ::= buildCall(Var, Locateds, Expr) [function]
                  | buildExpr(Located) [function]

    rule buildCall(F, Args, LastArg) => F(appendExpr(buildExprs(Args), LastArg))

    // TODO: Finish this
    rule buildExpr(X:Var) => X
    rule buildExpr(intConst(V)) => V
    rule buildExpr(boolConst(B)) => B
    rule buildExpr(strConst(S)) => S
    rule buildExpr(addrConst(Addr)) => Addr

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

    syntax KItem ::= flowNew(Locator, Var, Locators, Locator) [seqstrict(3,1,4)]
    rule A --> new T(Args) --> B => flowNew(locate(A), T, locateArgs(Args, .Locateds), locate(B))
    rule flowNew(Src, T, Args, Dst) => lookupValues(Src, construct(T, Args, Dst)) ~> appendStmts

    syntax KItem ::= flowTransformer(Locator, Var, Locators, Locator) [seqstrict(3,1,4)]
    rule (A --> F(Args) --> B):Stmt => flowTransformer(locate(A), F, locateArgs(Args, .Locateds), locate(B))
    rule flowTransformer(Src, F, Args, Dst) => lookupValues(Src, callTransformer(F, Args, Dst)) ~> appendStmts

    syntax Locators ::= locateArgs(Locators, Locators)
    rule locateArgs(.Locators, Res) => Res
    rule locateArgs((L:Locator, Ls), Res) => locate(L) ~> locateArgs(Ls, Res)
    rule L:Located ~> locateArgs(Ls, Res) => locateArgs(Ls, appendLoc(Res, L))

    syntax Locator ::= locate(Locator)

    rule locate(V:Int) => intConst(V)
    rule locate(B:Bool) => boolConst(B)
    rule locate(S:String) => strConst(S)
    rule locate(Addr:Hex) => addrConst(Addr)

    rule <k> locate([ Q T ; Locs ]) => locateEach(Q T, Locs, .List) ... </k>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax KItem ::= locateEach(Type, Locators, List)
    rule locateEach(T, .Locators, Res) => source(T, Res)
    rule locateEach(T, (L:Locator, Ls), Res) => locate(L) ~> locateEach(T, Ls, Res)
    rule Y:Located ~> locateEach(T, Locs, Res) => locateEach(T, Locs, Res ListItem(Y))

    rule <k> locate(record(Keys) { Members }) => locateRecordFields(genVar(!I), Members) ~> genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> record(Keys) { membersToDefs(Members) } ... </typeEnv>
        <compiled> ListItem(Ss:SolStmts => Ss (baseTypeToSolType(record(Keys) { membersToDefs(Members) }) memory genVar(!I);)) ... </compiled>
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

    rule <k> locate(var X : T) => X ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <compiled> ListItem(Ss:SolStmts => Ss (varDefToSolVar(X : any T);)) ... </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax KItem ::= locateSelector(Locator, Locator) [seqstrict]
    rule locate(L[K]) => locateSelector(locate(L), locate(K))
    rule locateSelector(L, K) => sourceSelect(L, K)

    syntax KItem ::= locateFilter(Locator, TypeQuant, Var, Locators) [seqstrict(4,1)]
    // TODO: Need to check that the args get evaluated correctly **BEFORE** the filtered collections
    rule locate(L[Q such that F(Args)]) => locateFilter(locate(L), Q, F, locateArgs(Args, .Locateds))
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
    // Tables with no keys are just implemented as arrays
    rule baseTypeToSolType(table(.Vars) _ T) => baseTypeToSolType(T)[]
    rule baseTypeToSolType(table(Keys) T) => nameOf(table(Keys) T)
        requires Keys =/=K .Vars

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

