// The syntax module containing the "core" flow language.
module FLOW-CORE-SYNTAX
    imports DOMAINS-SYNTAX

    syntax EmptyVal ::= "emptyval" [token]
    syntax Val ::= Int
                 | Bool
                 | String
                 | EmptyVal
                 | "\\" Id ":" Type "." Expr [binder]

    syntax QualifiedId ::= Id
                         | Storage "[" Expr "]" [strict(2)]
                         | Storage "." Storage [left]

    syntax SpecialStorage ::= "consume" [token]
                            | "new" QualifiedId "(" Exprs ")"
    syntax Storage ::= Val
                     | QualifiedId
                     | SpecialStorage

    /* syntax TupleExpr ::= "(" Exprs ")" // Tuples */

    syntax FunctionCall ::= Storage "(" Exprs ")"
    syntax Expr ::= Storage
                  | "(" Expr ")"        [bracket]
                  | "{" Exprs "}" // Set literals
                  /* | TupleExpr */
                  | FunctionCall
                  > Expr "or" Expr [strict(1)]
                  | Expr "and" Expr [strict(1)]
                  > Expr "+" Expr [left, seqstrict]
                  | Expr "-" Expr [left, seqstrict]
                  > Expr "=" Expr [seqstrict]
                  | Expr "<=" Expr [seqstrict]
                  | Expr "<" Expr [seqstrict]
                  > Selector "in" Storage [seqstrict]
                  > "not" Expr [strict]
                  > "if" Expr "then" Expr "else" Expr [strict(1)]
    syntax Vals ::= List{Val, ","} [klabel(exprs)]
    syntax Exprs ::= List{Expr, ","} [seqstrict, klabel(exprs)]
                   | Vals

    syntax SpecialSelect ::= "everything" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "!" [token]
                   | "any" [token]
                   | "nonempty" [token]
    syntax Selector ::= Expr
                      | SpecialSelect
                      | Quant Id ":" Type "such" "that" Expr [binder]

    syntax Flow ::= Storage
                  | Storage "--[" Selector "]->" Flow [strict(2)]

    // TODO: Maybe get rid of nonfungible or fungible and have be the default
    // TODO: Warn if people put consumable on non-asset types, because that's redundant.
    syntax Modifier ::= "nonfungible" [token]
                      | "fungible"    [token]
                      | "consumable"  [token]
                      | "asset"       [token]
                      | "copyable"    [token]
    syntax Modifiers ::= List{Modifier, " "}

    syntax TypeQuant ::= Quant
                       | "empty" [token]
                       | "every" [token]

    syntax Collection ::= "set" [token]
                        | "list" [token]
                        | "option" [token]
    syntax BaseType ::= QualifiedId
                      | Type "*" Type
                      | Type "~~>" Type
                      | Collection Type
                      | "(" Type ")" [bracket]
    // TODO: Add syntactic sugar that allows users to not always write the type quantity.
    syntax Type ::= TypeQuant BaseType

    syntax VarDef ::= Id ":" Type
    syntax VarDefs ::= List{VarDef, ","}
    syntax TypeDef ::= "type" Id "is" Modifiers BaseType
    syntax FieldDef ::= VarDef
                      | VarDef ":=" Expr
    syntax TransactionDef ::= "transaction" Id "(" VarDefs ")" "returns" Type ":" Stmt
    syntax Decl ::= TypeDef
                  | TransactionDef
                  | FieldDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | "var" VarDef ":=" Expr [strict(2)]
                  | "pass" [token]
                  | "return" Expr [strict]
                  | FunctionCall
                  | Stmt Stmt [right]

    // Add the built-in types to the Id sort so we can reference them in the rules
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]
                | "unit"       [token]
                | "void"       [token]
    // Special reserved Ids
    syntax Id ::= "this" [token]

    syntax Contract ::= "contract" Id "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Program ::= Contracts ";" Stmt
endmodule

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX
    imports FLOW-CORE-SYNTAX

    // All the new syntax here gets desugared at some point.
    syntax Expr ::= Expr ">=" Expr
                  | Expr ">" Expr
                  | Selector "not" "in" Storage
                  | Expr "!=" Expr

    // Quantifiers "speaking names"
    syntax Quant ::= "exactly" "one"

    syntax Flow ::= Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types

    syntax TransactionDef ::= "transaction" Id "(" VarDefs ")" ":" Stmt

    syntax Stmt ::= "var" VarDef

    rule var X : T => var X : T := emptyval [macro]

    // Desugaring
    rule S --> D => S --[ everything ]-> D [macro]

    rule S --[ Sel1 ]-> T:QualifiedId --[ Sel2 ]-> D
         =>
         (S --[ Sel1 ]-> T)
         (T --[ Sel2 ]-> D)
         [macro]

    rule S := E => (S --> consume) (E --> S) [macro]

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

