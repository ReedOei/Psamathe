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

    syntax FunctionCall ::= Var "(" Exprs ")"
    syntax IfExpr ::= "if" Expr "{" Expr "}" "else" "{" Expr "}" [strict(1), klabek(if)]
    syntax Expr ::= Val | EmptyVal | Int | Bool | String
                  | "\\" Var ":" Type "." Expr
                  | Var
                  | FunctionCall
                  | "some" "(" Expr ")" [strict]
                  | Selector "in" Source [strict(1)]
                  | "{" RecordMemberExprs "}"
                  | "let" VarDef ":=" Expr "in" Expr [strict(2)]
                  | IfExpr
                  | "(" Expr ")"        [bracket]
                  | "new" Var "(" Exprs ")"
                  > Expr "or" Expr [strict(1)]
                  | Expr "and" Expr [strict(1)]
                  > Expr "+" Expr [left, seqstrict]
                  | Expr "-" Expr [left, seqstrict]
                  > Expr "=" Expr [seqstrict]
                  | Expr "<=" Expr [seqstrict]
                  | Expr "<" Expr [seqstrict]
                  > "not" Expr [strict]
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

    syntax Flow ::= Source "--[" Selector "]->" Destination [strict(2)]

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
    syntax TransactionDef ::= "transaction" Var "(" VarDefs ")" "returns" Type ":" Stmt
    syntax Decl ::= TypeDef
                  | TransactionDef
                  | FieldDef
    syntax Decls ::= List{Decl, " "}

    syntax Revert ::= "revert" "(" Expr ")" [strict]
    syntax IfStmt ::= "if" Expr "{" Stmt "}" "else" "{" Stmt "}" [strict(1), klabel(if)]
                    | IfExpr
    syntax Stmt ::= Flow
                  | "var" VarDef ":=" Expr "in" Stmt [strict(2)]
                  | "pass"
                  | "pack"
                  | "unpack" "(" Var ")"
                  | "return" Expr [strict]
                  | Revert
                  | IfStmt
                  | Stmt Stmt [right]
                  > Expr

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
         transaction T(Args) returns ! bool: S (return true)
         [macro]
endmodule

