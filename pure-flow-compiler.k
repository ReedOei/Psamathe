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
                  > left: Expr "+" Expr
                  | Expr "-" Expr
                  > nonassoc: Expr "<" Expr
                  | Expr "==" Expr
    syntax Exprs ::= List{Expr, ","}

    syntax SolStmt ::= Expr ";"
                     | SolVar "=" Expr ";"
                     | SolVarDef
                     | Expr "=" Expr ";"
                     | "return" Var ";"
                     | "for" "(" SolStmt Expr ";" Expr ")" "{" SolStmts "}"
    syntax SolStmts ::= List{SolStmt, ""} [klabel(stmts)]

    syntax SolType ::= Var
                     | SolType "[]"
                     | "mapping" "(" SolType "=>" SolType ")"

    syntax Struct ::= "struct" Var "{" SolVarDefs "}"
    syntax Function ::= "function" Var "(" SolArgs ")" "returns" "(" SolVarDef ")" "{" SolStmts "}"
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

    syntax KResult ::= Var
                     | Vars

    // Variables we'll need to do code generation
    syntax Var ::= "success" | "keys" | "underlying_map" | "length" | "push"

    configuration
        <common />
        <k> $PGM:Program </k>
        <typeNameMap> .Map </typeNameMap>
        <structs> .Map </structs>
        <fields> .Map </fields>
        <functions> .Map </functions>
        <varMap> .Map </varMap>
        <compiled> .SolStmts </compiled>
        <typeEncoding> .Map </typeEncoding>

    syntax KItem ::= translateDecls(Decls)
                   | translateDecl(Decl)

    syntax KItem ::= "done"

    rule (Decls ; Stmts):Program => checkDecls(Decls) ~> checkStmts(Stmts) ~> translateDecls(Decls) ~> Stmts ~> done

    syntax KItem ::= checkDecls(Decls)
                   | checkDecl(Decl)
                   | checkStmts(Stmts)
                   | checkStmt(Stmt)

    rule checkDecls(.Decls) => .
    rule checkDecls(D Ds) => checkDecl(D) ~> checkDecls(Ds)

    // TODO: Implement this
    rule checkDecl(_) => .

    rule checkStmts(.Stmts) => .
    rule checkStmts(S1 Rest) => checkStmt(S1) ~> checkStmts(Rest)

    // TODO: Implement this
    rule checkStmt(_) => .

    // =========================================
    // Sequencing
    // =========================================
    rule .Stmts => . [structural]
    rule S1:Stmt Rest:Stmts => S1 ~> Rest [structural]

    syntax SolDecls ::= List2SolDecls(List) [function, functional]
    rule List2SolDecls(.List) => .SolDecls
    rule List2SolDecls(ListItem(D:SolDecl) Rest) => D List2SolDecls(Rest)

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
        <compiled> Body => .SolStmts </compiled>
        <structs> Structs </structs>
        <functions> Functions </functions>

    rule translateDecls(.Decls) => .
    rule translateDecls(D Ds) => translateDecl(D) ~> translateDecls(Ds)

    rule <k> translateDecl(type T is Ms BaseT) => . ... </k>
        <structs> Structs => Structs defineStructs(T, BaseT) </structs>
        <types> ... .Map => T |-> (type T is Ms BaseT) ... </types>
        <typeEncoding> ... .Map => T |-> encodeType(T, BaseT) ... </typeEncoding>

    syntax KItem ::= setupArgs(VarDefs)
                   | defFunc(Var)
                   | cleanupEnv(Set)

    rule translateDecl(transformer F(Args) -> X : _ T { Body }) => setupArgs(X : empty T, Args) ~> Body ~> defFunc(F) ~> cleanupEnv(keys(makeEnv(X : empty T, Args)))

    rule <k> cleanupEnv(Xs) => . ... </k>
        <typeEnv> Env => removeAll(Env, Xs) </typeEnv>

    syntax Map ::= makeEnv(VarDefs) [function, functional]
    rule makeEnv(.VarDefs) => .Map
    rule makeEnv(X : T, Rest) => (X |-> T) makeEnv(Rest)

    syntax Map ::= defineStructs(Var, BaseType) [function, functional]
                 | defineVarDefsStructs(VarDefs) [function, functional]

    rule defineStructs(_, nat) => .Map
    rule defineStructs(_, string) => .Map
    rule defineStructs(_, address) => .Map
    rule defineStructs(_, bool) => .Map
    rule defineStructs(_, list _ T) => defineStructs(nameOf(T), T)
    rule defineStructs(_, _:Var) => .Map
    rule defineStructs(T, { Fields }) => (T |-> struct T { encodeFields(Fields) }) defineVarDefsStructs(Fields)
    rule defineStructs(T, map _ T1 => _ T2) => T |-> struct T {
                                                        mapping (baseTypeToSolType(T1) => baseTypeToSolType(T2)) underlying_map;
                                                        baseTypeToSolType(T1)[] keys;
                                                     }
    rule defineVarDefsStructs(.VarDefs) => .Map
    rule defineVarDefsStructs(_ : _ T, Rest) => defineStructs(nameOf(T), T) defineVarDefsStructs(Rest)

    rule <k> A --> B => flow(locate(A, flowType(A, B)), locate(B, flowType(A, B))) ... </k>

    syntax KItem ::= flow(Locator, Locator) [strict]

    // =========================================
    // Flow for nats
    // =========================================
    rule <k> flow(X:Var, Y:Var) => . ... </k>
        <typeEnv> ... (X |-> nat) (Y |-> nat) ... </typeEnv>
        <compiled> S => S @ (Y = Y + X;) @ (X = 0;) </compiled>

    // TODO: Instead of the old approach, we should instead have a locateSource or something that evaluates to a list of things to send
    // TODO: Then we can implement list literals without actually building a list, and similarly for all filters and everything
    // TODO: So you build a block of code with filters and such into which we embed the transfer code
    // so locateSource([ a, b][ any such that f(_)]) gives us something like
    // for x in [a,b]:
    //      if f(x):
    //          ______ HERE IS A HOLE WHERE THE TRANSFER CODE GOES ______

    // =========================================
    // Flow list to map
    // =========================================
    rule <k> flow(X:Var, Y:Var) => . ... </k>
        <typeEnv>
            ...
            (X |-> list ! { key : K, value : V })
            (Y |-> map K => V)
            ...
        </typeEnv>
        <compiled>
            Cur
            =>
            Cur @
            for (uint genVar(I) = 0; genVar(I) < (X.length); genVar(I)++) {
                Y.underlying_map[X[genVar(I)].key] = X[genVar(I)].value;
                Y.keys.push(X[genVar(I)].key);
            }
        </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>

    syntax Locators ::= locateEach(Locators, VarDefs) [function, functional]
    rule locateEach(.Locators, .VarDefs) => .Locators
    rule locateEach((L:Locator, Ls), (_ : _ T, Xs)) => locate(L, T), locateEach(Ls, Xs)

    syntax KItem ::= flowNew(Locator, Var, Locators, Locators) [strict(1,3,4)]

    // TODO: This isn't quite right, because it won't handle a list correctly.
    rule <k> A --> new T(Locs) --> B => flowNew(
                                                A, /* locate(A, baseTypeOf(lastVDef(getConstructorArgs(BaseT)))), */
                                                T,
                                                locateEach(Locs, tailVDefs(getConstructorArgs(BaseT))),
                                                B) ... </k>
        <types> ... T |-> type T is _ BaseT ... </types>
    // TODO: Finish getConstructoArgs

    /* rule <k> flowNew(X:Var, T, Args:Vars, Y:Var) */

    syntax SolStmts ::= SolStmts "@" SolStmt [function, functional]
    rule .SolStmts @ B => B
    rule (S:SolStmt Rest:SolStmts) @ B => S (Rest @ B)

    syntax Locator ::= locate(Locator, BaseType)

    rule <k> locate(V:Int, nat) => genVar(I) ... </k>
        <typeEnv> ... .Map => genVar(I) |-> nat ... </typeEnv>
        <compiled> Ss => Ss @ (uint genVar(I) = V;) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>

    rule <k> locate([ .Locators ], list Q T) => genVar(I) ... </k>
        <typeEnv> ... .Map => genVar(I) |-> list Q T ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T)[] genVar(I);) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>
        <structs> Structs => Structs defineStructs(nameOf(T), T) </structs>

    rule <k> locate([ .Locators ], map K => V) => genVar(I) ... </k>
        <typeEnv> ... .Map => genVar(I) |-> list ! { key : K, value : V } ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType({ key : K, value : V })[] genVar(I);) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>
        <structs> Structs => Structs defineStructs(nameOf({ key : K, value : V }), { key : K, value : V }) </structs>

    rule locate(X:Var, _) => X
    rule locate(demote(L), T) => locate(L, T)

    context locate(copy(HOLE => locate(copy(HOLE), T)), T)
    rule <k> locate(copy(X:Var), T) => X ... </k>
        <typeEnv> ... .Map => genVar(I) |-> T ... </typeEnv>
        // TODO: Does this actually copy everything?
        <compiled> Ss => Ss @ (baseTypeToSolType(T) genVar(I) = X;) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>

    rule <k> locate(var X : T, T) => X ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T) X;) </compiled>
        <structs> Structs => Structs defineStructs(nameOf(T), T) </structs>

    syntax Var ::= nameOf(BaseType) [function, functional]
    rule nameOf(X:Var) => X
    rule nameOf({ Fields }) => String2Id(genName(Fields))
    rule nameOf(map T1 => T2) => String2Id(baseTypeToString(map T1 => T2))

    syntax String ::= typeToString(Type) [function, functional]
                    | baseTypeToString(BaseType) [function, functional]
                    | quantToString(TypeQuant) [function, functional]
                    | genName(VarDefs) [function, functional]
    rule genName(.VarDefs) => ""
    rule genName(X : T, Fields) => baseTypeToString(X) +String "__" +String typeToString(T) +String genName(Fields)

    rule quantToString(any) => "any"
    rule quantToString(!) => "one"
    rule quantToString(nonempty) => "nonempty"
    rule quantToString(empty) => "empty"
    rule quantToString(every) => "every"

    rule typeToString(Q T) => quantToString(Q) +String baseTypeToString(T)

    rule baseTypeToString(nat) => "nat"
    rule baseTypeToString(string) => "string"
    rule baseTypeToString(bool) => "bool"
    rule baseTypeToString(address) => "address"
    // NOTE: Kind of annoying I need to define this for every special variable I add. Avoidable?
    rule baseTypeToString(key) => "key"
    rule baseTypeToString(value) => "value"
    rule baseTypeToString(X:Id) => Id2String(X)
    rule baseTypeToString(X.Y) => baseTypeToString(X) +String "___" +String baseTypeToString(Y)
    rule baseTypeToString({ Fields }) => genName(Fields)
    rule baseTypeToString(map T1 => T2) => "map_" +String typeToString(T1) +String "_to_" +String typeToString(T2)

    syntax Id ::= genVar(Int) [function, functional]
    rule genVar(I) => String2Id("v" +String Int2String(I))

    syntax SolType ::= typeToSolType(Type) [function, functional]
                     | baseTypeToSolType(BaseType) [function, functional]

    rule typeToSolType(_:TypeQuant T) => baseTypeToSolType(T)
    rule baseTypeToSolType(bool) => bool
    rule baseTypeToSolType(nat) => uint
    rule baseTypeToSolType(string) => string
    rule baseTypeToSolType(address) => address
    rule [[ baseTypeToSolType(X:Var) => SolT ]]
        <typeEncoding> ... X |-> SolT ... </typeEncoding>
    rule baseTypeToSolType(map T1 => T2) => nameOf(map T1 => T2)
    rule baseTypeToSolType({ Fields }) => nameOf({ Fields })

    syntax SolType ::= encodeType(Var, BaseType) [function, functional]
    rule encodeType(_, nat) => baseTypeToSolType(nat)
    rule encodeType(_, string) => baseTypeToSolType(string)
    rule encodeType(_, address) => baseTypeToSolType(address)
    rule encodeType(_, bool) => baseTypeToSolType(bool)
    rule encodeType(_, map T1 => T2) => baseTypeToSolType(map T1 => T2)
    rule encodeType(T, { _ }) => T

    syntax SolVarDefs ::= encodeFields(VarDefs) [function, functional]
    rule encodeFields(.VarDefs) => .SolVarDefs
    rule encodeFields(X : T, Fields) => (typeToSolType(T) X;) encodeFields(Fields)
endmodule

