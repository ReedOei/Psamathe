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

module PURE-FLOW-COMPILER-SYNTAX
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
                     | "demote" "(" Locator ")"
                     | "copy" "(" Locator ")"
                     | "var" Var ":" BaseType
    syntax Locators ::= List{Locator, ","}

    syntax Stmt ::= Locator "-->" Locator
                  | Locator "-->" Id "(" Vars ")" "-->" Locator
                  | "try" "{" Stmts "}" "catch" "{" Stmts "}"
    syntax Stmts ::= List{Stmt, " "} [klabel(stmts)]

    syntax Decl ::= "type" Id "is" Modifiers BaseType
                  | "transformer" Id "(" VarDefs ")" "->" VarDef "{" Stmts "}"
    syntax Decls ::= List{Decl, " "}

    syntax Program ::= Decls ";" Stmts
endmodule

module PURE-FLOW-COMPILER
    imports PURE-FLOW-COMPILER-SYNTAX
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

    syntax SolStmts ::= SolStmts "@" SolStmt [function, functional]
    rule .SolStmts @ B => B
    rule (S:SolStmt Rest:SolStmts) @ B => S (Rest @ B)

    syntax BaseType ::= flowType(Locator, Locator) [function, functional]
    rule flowType(_:Int, _) => nat
    rule flowType(_, _:Int) => nat
    rule flowType(var _ : T, _) => T
    rule flowType(_, var _ : T) => T
    rule [[ flowType(X, _) => T ]]
        <typeEnv> ... X |-> T ... </typeEnv>
    rule [[ flowType(_, X) => T ]]
        <typeEnv> ... X |-> T ... </typeEnv>
    rule flowType(demote(A), B) => demoteBaseType(flowType(A, B))
    rule flowType(A, demote(B)) => demoteBaseType(flowType(A, B))
    rule flowType(copy(A), B) => demoteBaseType(flowType(A, B))
    rule flowType(A, copy(B)) => demoteBaseType(flowType(A, B))

    syntax BaseType ::= demoteBaseType(BaseType) [function, functional]

    rule demoteBaseType(nat) => nat
    rule demoteBaseType(string) => string
    rule demoteBaseType(address) => address
    rule demoteBaseType(bool) => bool
    rule [[ demoteBaseType(T1) => demoteBaseType(T2) ]]
        <types> ... T1 |-> (type _ is _ T2) ... </types>
    rule demoteBaseType(list Q T) => list Q demoteBaseType(T)
    rule demoteBaseType(map Q1 T1 => Q2 T2) => map Q1 demoteBaseType(T1) => Q2 demoteBaseType(T2)
    rule demoteBaseType({ Fields }) => { demoteVarDefs(Fields) }

    syntax VarDefs ::= demoteVarDefs(VarDefs) [function, functional]
    rule demoteVarDefs(.VarDefs) => .VarDefs
    rule demoteVarDefs(X : Q T, Rest) => X : Q demoteBaseType(T), demoteVarDefs(Rest)

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

