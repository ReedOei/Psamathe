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
                  > nonassoc: Expr "<" Expr
                  | Expr "==" Expr
    syntax Exprs ::= List{Expr, ","}

    syntax SolField ::= Var ":" Expr
    syntax SolFields ::= List{SolField, ","}

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
        <typeNameMap> .Map </typeNameMap>
        <structs> .Map </structs>
        <fields> .Map </fields>
        <compiled> .SolStmts </compiled>
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

    rule run(Stmts) => Stmts ~> done

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

    rule <k> translateDecl(type T is Ms BaseT) => . ... </k>
        <structs> Structs => Structs defineStructs(T, BaseT) </structs>
        <types> ... .Map => T |-> typeDef(modifiersToSet(Ms), BaseT) ... </types>
        <typeEncoding> ... .Map => T |-> encodeType(T, BaseT) ... </typeEncoding>

    syntax KItem ::= setupArgs(VarDefs)
                   | defFunc(Var)
                   | cleanupEnv(Set)

    rule translateDecl(transformer F(Args) -> X : _ T { Body }) => setupArgs(X : empty T, Args) ~> Body ~> defFunc(F) ~> cleanupEnv(keys(makeEnv(X : empty T, Args)))

    rule <k> cleanupEnv(Xs) => . ... </k>
        <typeEnv> Env => removeAll(Env, Xs) </typeEnv>

    syntax Map ::= defineStructs(Var, BaseType) [function, functional]
                 | defineVarDefsStructs(VarDefs) [function, functional]

    rule defineStructs(_, nat) => .Map
    rule defineStructs(_, string) => .Map
    rule defineStructs(_, address) => .Map
    rule defineStructs(_, bool) => .Map
    rule defineStructs(_, table(_) _ T) => defineStructs(nameOf(T), T)
    rule defineStructs(_, _:Var) => .Map
    rule defineStructs(T, record(_) { Fields }) => (T |-> struct T { encodeFields(Fields) }) defineVarDefsStructs(Fields)
    rule defineStructs(T, map _ T1 => _ T2) => T |-> struct T {
                                                        mapping (baseTypeToSolType(T1) => baseTypeToSolType(T2)) underlying_map;
                                                        baseTypeToSolType(T1)[] keys;
                                                     }
    rule defineVarDefsStructs(.VarDefs) => .Map
    rule defineVarDefsStructs(_ : _ T, Rest) => defineStructs(nameOf(T), T) defineVarDefsStructs(Rest)

    rule <k> A --> B => flow(locate(A), locate(B)) ... </k>

    syntax KItem ::= flow(Locator, Locator) [seqstrict]

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
            (X |-> table(_) _ record(_) { key : K, value : V})
            (Y |-> map K => V)
            ...
        </typeEnv>
        <compiled>
            Cur
            =>
            Cur @
            for (uint genVar(!I) = 0; genVar(!I) < (X.keys.length); genVar(!I)++) {
                Y.underlying_map[X[genVar(!I)].key] = X[genVar(!I)].value;
                Y.keys.push(X[genVar(!I)].key);
            }
        </compiled>

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

    syntax SolStmts ::= SolStmts "@" SolStmt [function, functional]
    rule .SolStmts @ B => B
    rule (S:SolStmt Rest:SolStmts) @ B => S (Rest @ B)

    syntax Locator ::= locate(Locator)

    rule <k> locate(V:Int) => genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> nat ... </typeEnv>
        <compiled> Ss => Ss @ (uint genVar(!I) = V;) </compiled>

    rule <k> locate([ Q T ; Locs ]) => locateEach(genVar(!I), Locs) ~> genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> list Q T ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T)[] genVar(!I);) </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

    syntax KItem ::= locateEach(Var, Locators)
    rule locateEach(_, .Locators) => .
    rule locateEach(X, (L:Locator, Ls)) => locate(L) ~> locateEach(X, Ls)
    rule <k> Y:Var ~> locateEach(X, Locs) => locateEach(X, Locs) ... </k>
        <compiled> Ss => Ss @ (X.push(Y);) </compiled>

    rule <k> locate(record(Keys) { Members }) => locateRecordFields(genVar(!I), Members) ~> genVar(!I) ... </k>
        <typeEnv> ... .Map => genVar(!I) |-> record(Keys) { membersToDefs(Members) } ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(record(Keys) { membersToDefs(Members) }) genVar(!I);) </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(record(Keys) { membersToDefs(Members) }), record(Keys) { membersToDefs(Members) })) </structs>

    syntax KItem ::= locateRecordFields(Var, RecordMembers)
                   | setField(Var, Var)
    rule locateRecordFields(_, .RecordMembers) => .
    rule locateRecordFields(X, ((F : _ |-> V), Rest:RecordMembers))
         => locate(V) ~> setField(X, F) ~> locateRecordFields(X, Rest)

    rule <k> Y:Var ~> setField(X, F) => . ... </k>
        <compiled> Ss => Ss @ (X.F = Y;) </compiled>

    rule locate(X:Var) => X
    rule locate(demote(L)) => locate(L)

    context locate(copy(HOLE => locate(copy(HOLE))))
    rule <k> locate(copy(X:Var)) => X ... </k>
        // TODO: Does this actually copy everything?
        <compiled> Ss => Ss @ (baseTypeToSolType(T) genVar(!I) = X;) </compiled>
        <typeEnv> ... (X |-> T) (.Map => genVar(!I) |-> T) ... </typeEnv>

    rule <k> locate(var X : T) => X ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T) X;) </compiled>
        <structs> Structs => union(Structs, defineStructs(nameOf(T), T)) </structs>

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
    rule baseTypeToSolType(record(Keys) { Fields }) => nameOf(record(Keys) { Fields })

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

