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

    syntax Locator ::= Bool | Int | Var | "[" Locators "]" | "var" Var ":" BaseType
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

    syntax KResult

    configuration
        <T>
            <k> $PGM:Program </k>
            <structs> .Map </structs>
            <fields> .Map </fields>
            <functions> .Map </functions>
            <constructorBody> .SolStmts </constructorBody>
            <typeEnv> .Map </typeEnv>
            <varMap> .Map </varMap>
            <compiled> .SolStmts </compiled>
            <scopeStack> .List </scopeStack>
            <freshCounter> 0 </freshCounter>
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
        <constructorBody> Body </constructorBody>

    rule translateDecls(.Decls) => .
    rule translateDecls(D Ds) => translateDecl(D) ~> translateDecls(Ds)

    rule skip => .

    rule <k> A --> B => locate(A, genVar(I)) ~> locate(B, genVar(I +Int 1)) ~> flow(genVar(I), genVar(I +Int 1)) ... </k>
        <freshCounter> I => I +Int 2 </freshCounter>

    syntax Stmt ::= flow(Var, Var)

    // Flow for uints
    rule <k> flow(X, Y) => . ... </k>
        <typeEnv> ... (X |-> uint) (Y |-> uint) ... </typeEnv>
        <compiled> S => S @ (Y = Y + X;) @ (X = 0;) </compiled>

    syntax SolStmts ::= SolStmts "@" SolStmt [function, functional]
    rule .SolStmts @ B => B
    rule (S:SolStmt Rest:SolStmts) @ B => S (Rest @ B)

    syntax Stmt ::= locate(Locator, Var)

    rule <k> locate(I:Int, X) => . ... </k>
        <typeEnv> ... .Map => X |-> uint ... </typeEnv>
        <compiled> Ss => Ss @ (uint X = I;) </compiled>

    rule <k> locate(X:Var, Y) => . ... </k>
        <varMap> ... X |-> Z ... </varMap>
        <typeEnv> ... (Z |-> T) .Map => Y |-> T ... </typeEnv>
        <compiled> Ss => Ss @ (T:SolType Y = Z;)</compiled>

    rule <k> locate(var X : T, Y) => . ... </k>
        <varMap> ... .Map => X |-> Y ... </varMap>
        <typeEnv> ... .Map => Y |-> baseTypeToSolType(T) ... </typeEnv>
        <compiled> Ss => Ss @ (baseTypeToSolType(T) Y;) </compiled>

    syntax Id ::= genVar(Int) [function, functional]
    rule genVar(I) => String2Id("v" +String Int2String(I))

    syntax SolType ::= typeToSolType(Type) [function, functional]
                     | baseTypeToSolType(BaseType) [function, functional]

    rule typeToSolType(_:TypeQuant T) => baseTypeToSolType(T)
    rule baseTypeToSolType(bool) => bool
    rule baseTypeToSolType(nat) => uint
endmodule

