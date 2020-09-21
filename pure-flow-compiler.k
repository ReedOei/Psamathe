module VARS
    imports DOMAINS-SYNTAX

    syntax Var ::= Id
                 | Var "." Id

    syntax Vars ::= List{Var, ","}

    syntax Var ::= "bool" | "uint" | "address" | "string" | "nat"
endmodule

module SOLIDITY-SYNTAX
    imports DOMAINS-SYNTAX
    imports VARS

    // Some special variables
    syntax Var ::= "this" | "msg" | "sender" | "value"

    syntax SolVar ::= SolType Var
    syntax SolArgs ::= List{SolVar, ","}

    syntax SolVarDef ::= SolVar ";"
    syntax SolVarDefs ::= List{SolVarDef, " "}

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
    syntax SolStmts ::= List{SolStmt, " "} [klabel(stmts)]

    syntax SolType ::= Var
                     | SolType "[]"
                     | "mapping" "(" SolType "=>" SolType ")"

    syntax Struct ::= "struct" Var "{" SolVarDefs "}"
    syntax Function ::= "function" Var "(" SolArgs ")" "returns" "(" SolVarDef ")" "{" SolStmts "}"
    syntax Constructor ::= "constructor" "(" SolArgs ")" "{" SolStmts "}"

    syntax SolDecl ::= Struct | Function | Constructor | SolVarDef

    syntax SolDecls ::= List{SolDecl, " "}
    syntax Contract ::= "contract" Var "{" SolDecls "}"
endmodule

module PURE-FLOW-TO-SOLIDITY-SYNTAX
    imports DOMAINS-SYNTAX
    imports VARS

    syntax Modifier ::= "fungible"
                      | "immutable"
                      | "unique"
                      | "consumable"
                      | "asset"
    syntax Modifiers ::= List{Modifier, " "}

    syntax TypeQuant ::= "!" | "any" | "nonempty" | "empty" | "every"
    syntax RecordType ::= "{" VarDefs "}"
    syntax BaseType ::= Var
                      | "list" Type
                      | "map" Type "=>" Type
                      | RecordType
                      | "(" BaseType ")" [bracket]
    syntax Type ::= TypeQuant BaseType

    syntax VarDef ::= Var ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax RecordMember ::= Var ":" Type "|->" Var
    syntax RecordMembers ::= List{RecordMember, ","}

    syntax Locator ::= Bool | Int | Var
                     | Locator "." Var
                     | "[" Locators "]"
                     | "{" RecordMembers "}"
                     | "var" Var ":" BaseType
    syntax Locators ::= List{Locator, ","}

    syntax Stmt ::= "skip"
                  | Locator "-->" Locator
                  | Locator "-->" Id "(" Vars ")" "-->" Locator
                  | "try" "{" Stmts "}" "catch" "{" Stmts "}"
    syntax Stmts ::= List{Stmt, " "} [klabel(stmts)]

    syntax Decl ::= "type" Id "is" Modifiers BaseType
                  | "transformer" Id "(" VarDefs ")" "->" VarDef "{" Stmts "}"
    syntax Decls ::= List{Decl, " "}

    syntax Program ::= Decls ";" Stmts
endmodule

module PURE-FLOW-TO-SOLIDITY
    imports PURE-FLOW-TO-SOLIDITY-SYNTAX
    imports SOLIDITY-SYNTAX
    imports DOMAINS
    imports COLLECTIONS

    syntax KResult ::= Var

    // Variables we'll need to do code generation
    syntax Var ::= "success" | "keys" | "underlying_map" | "length" | "push" | "key"

    configuration
        <T>
            <k> $PGM:Program </k>
            <typeNameMap> .Map </typeNameMap>
            <structs> .Map </structs>
            <fields> .Map </fields>
            <functions> .Map </functions>
            <typeEnv> .Map </typeEnv>
            <varMap> .Map </varMap>
            <compiled> .SolStmts </compiled>
            <freshCounter> 0 </freshCounter>
            <types> .Map </types>
            <typeEncoding> .Map </typeEncoding>
        </T>

    syntax KItem ::= scope(Map, Map)

    syntax KItem ::= translateDecls(Decls)
                   | translateDecl(Decl)

    syntax KItem ::= "done"

    rule (Decls ; Stmts):Program => translateDecls(Decls) ~> Stmts ~> done

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

    syntax SolType ::= encodeType(Var, BaseType) [function, functional]
    syntax SolVarDefs ::= encodeFields(VarDefs) [function, functional]
    syntax Map ::= defineStructs(Var, BaseType) [function, functional]
                 | defineVarDefsStructs(VarDefs) [function, functional]
    rule encodeType(_, nat) => baseTypeToSolType(nat)
    rule encodeType(_, string) => baseTypeToSolType(string)
    rule encodeType(_, address) => baseTypeToSolType(address)
    rule encodeType(_, bool) => baseTypeToSolType(bool)
    rule encodeType(_, map T1 => T2) => baseTypeToSolType(map T1 => T2)
    rule encodeType(T, { _ }) => T

    // TODO: Need to handle nested structs
    rule defineStructs(_, nat) => .Map
    rule defineStructs(_, string) => .Map
    rule defineStructs(_, address) => .Map
    rule defineStructs(_, bool) => .Map
    rule defineStructs(_, list _ T) => defineStructs(nameOf(T), T)
    rule defineStructs(T, { Fields }) => (T |-> struct T { encodeFields(Fields) }) defineVarDefsStructs(Fields)
    rule defineStructs(T, map _ T1 => _ T2) => T |-> struct T {
                                                        mapping (baseTypeToSolType(T1) => baseTypeToSolType(T2)) underlying_map;
                                                        baseTypeToSolType(T1)[] keys;
                                                     }
    rule defineVarDefsStructs(.VarDefs) => .Map
    rule defineVarDefsStructs(_ : _ T, Rest) => defineStructs(nameOf(T), T) defineVarDefsStructs(Rest)

    rule encodeFields(.VarDefs) => .SolVarDefs
    rule encodeFields(X : T, Fields) => (typeToSolType(T) X;) encodeFields(Fields)

    rule skip => .

    context (HOLE => locate(HOLE)) --> _
    context _ --> (HOLE => locate(HOLE))
    rule <k> A --> B => flow(A, B) ... </k>

    syntax Stmt ::= flow(Var, Var)

    // =========================================
    // Flow for nats
    // =========================================
    rule <k> flow(X, Y) => . ... </k>
        <typeEnv> ... (X |-> nat) (Y |-> nat) ... </typeEnv>
        <compiled> S => S @ (Y = Y + X;) @ (X = 0;) </compiled>

    // =========================================
    // Flow list to map
    // =========================================
    rule <k> flow(X, Y) => . ... </k>
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

    syntax SolStmts ::= SolStmts "@" SolStmt [function, functional]
    rule .SolStmts @ B => B
    rule (S:SolStmt Rest:SolStmts) @ B => S (Rest @ B)

    syntax Var ::= locate(Locator)

    rule <k> locate(V:Int) => locate(genVar(I)) ... </k>
        <typeEnv> ... .Map => genVar(I) |-> nat ... </typeEnv>
        <compiled> Ss => Ss @ (uint genVar(I) = V;) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>

    rule <k> locate([ .Locators ]) => locate(genVar(I)) ... </k>
        <typeEnv> ... .Map => genVar(I) |-> list ?_ ?T ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(?T)[] genVar(I);) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>
        <structs> Structs => Structs defineStructs(nameOf(?T), ?T) </structs>

    rule <k> locate(X:Var) => locate(X) ... </k>

    rule <k> locate(var X : T) => locate(X) ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T) X;) </compiled>
        <structs> Structs => Structs defineStructs(nameOf(T), T) </structs>

    syntax Var ::= nameOf(BaseType) [function, functional]
    rule nameOf(bool) => bool
    rule nameOf(nat) => nat
    rule nameOf(string) => string
    rule nameOf(address) => address
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
    rule baseTypeToSolType(X:Var) => X
    rule baseTypeToSolType(map (_:TypeQuant T1) => (_:TypeQuant T2)) => mapping (baseTypeToSolType(T1) => baseTypeToSolType(T2))
    rule baseTypeToSolType({ Fields }) => nameOf({ Fields })
endmodule

