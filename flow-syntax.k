// The syntax module containing the "core" flow language.
module FLOW-CORE-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Var ::= Id
                 | Var "." Var [left]

    // Add the built-in types to the Var sort so we can reference them in the rules
    syntax Var ::= "nat"
                | "bool"
                | "string"
                | "address"
                | "unit"
                | "void"
    // Special reserved Ids
    syntax Var ::= "this"
    // For generated Vars
    syntax Var ::= var(Int)

    syntax SelectorQuant ::= "!" | "any" | "nonempty"
    syntax TypeQuant ::= SelectorQuant | "empty" | "every"
    syntax Collection ::= "option" | "set" | "list"
    syntax BaseType ::= Var | Collection Type | Type "~~>" Type | "{" VarDefs "}"
                      | "(" Type ")" [bracket]
    // TODO: Add syntactic sugar that allows users to not always write the type quantity.
    syntax Type ::= TypeQuant BaseType

    syntax EmptyVal ::= "emptyval"

    syntax Val
    syntax Vals ::= List{Val, ","} [klabel(exprs)]

    syntax RecordMemberVal ::= Var ":" Type "|->" Val   [klabel(recordMember)]
    syntax RecordMemberExpr ::= Var ":" Type "|->" Expr [klabel(recordMember)]
                              | RecordMemberVal
    syntax RecordMemberVals ::= List{RecordMemberVal, ","} [klabel(recordMembers)]
    syntax RecordMemberExprs ::= List{RecordMemberExpr, ","} [klabel(recordMembers)]
                               | RecordMemberVals

    syntax FunctionCall ::= Var "(" Exprs ")" [klabel(funccall)]
    syntax IfExpr ::= "if" Expr "{" Expr "}" "else" "{" Expr "}" [klabek(if)]
    syntax Expr ::= Val | EmptyVal | Int | Bool | String
                  | "\\" Var ":" Type "." Expr
                  | Var
                  | FunctionCall
                  | "some" "(" Expr ")"
                  | Selector "in" Source
                  | "{" RecordMemberExprs "}"
                  | "let" VarDef ":=" Expr "in" Expr
                  | IfExpr
                  | "(" Expr ")"        [bracket]
                  | "new" Var "(" Exprs ")"
                  > "not" Expr
                  > Expr "or" Expr [left]
                  > Expr "and" Expr [left]
                  > Expr "+" Expr [left]
                  | Expr "-" Expr [left]
                  > Expr "=" Expr
                  | Expr "<=" Expr
                  | Expr "<" Expr
                  > IfExpr
    syntax Exprs ::= List{Expr, ","} [klabel(exprs)]

    syntax SourceVal ::= "new" Var
    syntax Source ::= Expr
                    | SourceVal
    syntax DestinationVal ::= "consume"
    syntax Destination ::= Expr
                         | DestinationVal
    syntax StorageVal ::= SourceVal | DestinationVal
    syntax Storage ::= Source | Destination | StorageVal

    syntax SelectorVal ::= Val | "everything"
    syntax Selector ::= Expr
                      | SelectorVal
                      | SelectorQuant VarDef "such" "that" Expr

    syntax Flow ::= Source "--[" Selector "]->" Destination

    // TODO: Maybe get rid of nonfungible or fungible and have be the default
    // TODO: Warn if people put consumable on non-asset types, because that's redundant.
    syntax Modifier ::= "nonfungible"
                      | "fungible"
                      | "consumable"
                      | "asset"
                      | "copyable"
    syntax Modifiers ::= List{Modifier, " "}

    syntax VarDef ::= Var ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax TypeDef ::= "type" Var "is" Modifiers BaseType
    syntax FieldDef ::= VarDef
    syntax TransactionDef ::= "transaction" Var "(" VarDefs ")" "returns" VarDef ":" Stmt
    syntax Decl ::= TypeDef
                  | TransactionDef
                  | FieldDef
    syntax Decls ::= List{Decl, " "}

    syntax Revert ::= "revert" "(" Expr ")"
    syntax IfStmt ::= "if" Expr "{" Stmt "}" "else" "{" Stmt "}" [klabel(if)]
                    | IfExpr
    syntax ReturnExpr ::= "return" Expr [klabel(returnexpr)]
    syntax Stmt ::= Flow
                  | "var" VarDef ":=" Expr "in" Stmt
                  | "pass"
                  | "pack"
                  | "unpack" "(" Var ")"
                  | "expr" "(" Expr ")"
                  | ReturnExpr
                  | Revert
                  | IfStmt
                  | FunctionCall
                  | "exit"
                  > Stmt Stmt [right, klabel(stmtseq)]

    syntax Contract ::= "contract" Var "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Program ::= Contracts ";" Stmt
endmodule

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX
    imports FLOW-CORE-SYNTAX
    imports DOMAINS

    syntax KResult

    // All the new syntax here gets desugared at some point.
    syntax Expr ::= Expr ">=" Expr
                  | Expr ">" Expr
                  | Selector "not" "in" Source
                  | Expr "!=" Expr

    // Quantifiers "speaking names"
    syntax Quant ::= "exactly" "one"

    syntax Flow ::= Source "-->" Destination
                  | Expr ":=" Expr // Assignment only allowed for consumable types

    syntax TransactionDef ::= "transaction" Var "(" VarDefs ")" ":" Stmt
                            | "transaction" Var "(" VarDefs ")" "returns" Type ":" Stmt

    syntax Stmt ::= "var" VarDef
                  // NOTE: The following is desugared by normalize(), because it's a little more complicated than the rest of the macros in this module
                  | "var" VarDef ":=" Expr
                  | "if" Expr "{" Stmt "}"

    rule var X : T => var X : T := emptyval [macro]

    // Desugaring
    rule S --> D => S --[ everything ]-> D [macro]

    // TODO: Allow these pipelines again?
    /* rule S --[ Sel1 ]-> T:QualifiedId --[ Sel2 ]-> D */
    /*      => */
    /*      (S --[ Sel1 ]-> T) */
    /*      (T --[ Sel2 ]-> D) */
    /*      [macro] */

    rule S := E => (S --> consume) (E --> S) [macro]

    rule if E { S } => if E { S } else { pass } [macro]

    rule A > B => B < A [macro]
    rule A >= B => B <= A [macro]
    rule A != B => not (A = B) [macro]

    rule F:Selector not in S => not (F in S) [macro]

    rule exactly one => ! [macro]

    rule transaction T(Args): S
         =>
         transaction T(Args) returns ! bool: S (return true):ReturnExpr
         [macro]
endmodule

