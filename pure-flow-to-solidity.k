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

    syntax SolVar ::= SolType Var
    syntax SolArgs ::= List{SolVar, ","}

    syntax SolVarDef ::= SolVar ";"
    syntax SolVarDefs ::= List{SolVarDef, " "}

    syntax Expr ::= Bool | Int | Var | Expr "." Var | Expr "+" Expr | Expr "-" Expr

    syntax SolStmt ::= SolVar "=" Expr ";"
                     | SolVarDef
                     | Var "=" Expr ";"
                     | "return" Var ";"
    syntax SolStmts ::= List{SolStmt, " "} [klabel(stmts)]

    syntax SolType ::= Var

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

    configuration
        <T>
            <k> $PGM:Program </k>
            <typeNameMap> .Map </typeNameMap>
            <structs> .Map </structs>
            <fields> .Map </fields>
            <functions> .Map </functions>
            <constructorBody> .SolStmts </constructorBody>
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

    syntax KItem ::= "putCtor"
                   | "done"

    rule <k> putCtor => . ... </k>
        <constructorBody> _ => Body </constructorBody>
        <compiled> Body => .SolStmts </compiled>

    rule (Decls ; Stmts):Program => translateDecls(Decls) ~> Stmts ~> putCtor ~> done

    rule .Stmts => . [structural]
    rule S1:Stmt Rest:Stmts => S1 ~> Rest [structural]

    rule <k> done
             =>
             contract String2Id("C") {
                constructor( .SolArgs ) {
                    Body
                }
            }
         </k>
        <constructorBody> Body => .SolStmts </constructorBody>

    rule translateDecls(.Decls) => .
    rule translateDecls(D Ds) => translateDecl(D) ~> translateDecls(Ds)

    // TODO: Need to deal with the modifiers eventually probably (mostly for fungible for combine impl. and unique so we generate the checker)
    // TODO: Would be good to encode T **directly** as BaseT (so if BaseT is not a struct, then don't encode as a struct).
    rule <k> translateDecl(type T is Ms BaseT) => . ... </k>
        <structs> Structs => Structs defineStructs(T, BaseT) </structs>
        <types> ... .Map => T |-> (type T is Ms BaseT) ... </types>
        <typeEncoding> ... .Map => T |-> encodeType(T, BaseT) ... </typeEncoding>

    syntax SolType ::= encodeType(Var, BaseType) [function, functional]
    syntax SolVarDefs ::= encodeFields(VarDefs) [function, functional]
    syntax Map ::= defineStructs(Var, BaseType) [function, functional]
    rule encodeType(_, nat) => uint
    rule encodeType(_, string) => string
    rule encodeType(_, address) => address
    rule encodeType(_, bool) => bool
    rule encodeType(T, { _ }) => T

    // TODO: Need to handle nested structs
    rule defineStructs(_, nat) => .Map
    rule defineStructs(_, string) => .Map
    rule defineStructs(_, address) => .Map
    rule defineStructs(_, bool) => .Map
    rule defineStructs(T, { Fields }) => T |-> struct T { encodeFields(Fields) }

    rule encodeFields(.VarDefs) => .SolVarDefs
    rule encodeFields(X : T, Fields) => (typeToSolType(T) X;) encodeFields(Fields)

    rule skip => .

    context (HOLE => locate(HOLE)) --> _
    context _ --> (HOLE => locate(HOLE))
    rule <k> A --> B => flow(A, B) ... </k>

    syntax Stmt ::= flow(Var, Var)

    // Flow for uints
    rule <k> flow(X, Y) => . ... </k>
        <typeEnv> ... (X |-> uint) (Y |-> uint) ... </typeEnv>
        <compiled> S => S @ (Y = Y + X;) @ (X = 0;) </compiled>

    syntax SolStmts ::= SolStmts "@" SolStmt [function, functional]
    rule .SolStmts @ B => B
    rule (S:SolStmt Rest:SolStmts) @ B => S (Rest @ B)

    syntax Var ::= locate(Locator)

    rule <k> locate(V:Int) => locate(genVar(I)) ... </k>
        <typeEnv> ... .Map => genVar(I) |-> uint ... </typeEnv>
        <compiled> Ss => Ss @ (uint genVar(I) = V;) </compiled>
        <freshCounter> I => I +Int 1 </freshCounter>

    rule <k> locate(X:Var) => locate(X) ... </k>

    rule <k> locate(var X : T) => locate(X) ... </k>
        <typeEnv> ... .Map => X |-> baseTypeToSolType(T) ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T) X;) </compiled>

    syntax Id ::= genVar(Int) [function, functional]
    rule genVar(I) => String2Id("v" +String Int2String(I))

    syntax SolType ::= typeToSolType(Type) [function, functional]
                     | baseTypeToSolType(BaseType) [function, functional]

    rule typeToSolType(_:TypeQuant T) => baseTypeToSolType(T)
    rule baseTypeToSolType(bool) => bool
    rule baseTypeToSolType(nat) => uint
    rule baseTypeToSolType(string) => string
    rule baseTypeToSolType(address) => address
endmodule

