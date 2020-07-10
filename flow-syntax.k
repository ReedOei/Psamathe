// The syntax module containing the "core" flow language.
module FLOW-CORE-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
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

    syntax Expr ::= Storage
                  | "(" Expr ")"        [bracket]
                  | "{" Exprs "}" // Set literals
                  /* | TupleExpr */
                  | Storage "(" Exprs ")" // Function call
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
                           | "nothing" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "!"
                   | "*"
                   | "+"
    syntax Selector ::= Expr
                      | SpecialSelect
                      | Quant Id ":" Type "such" "that" Expr [binder]

    syntax Flow ::= Storage
                  | Storage "--[" Selector "]->" Flow [strict]

    // TODO: Maybe get rid of nonfungible or fungible and have be the default
    // TODO: Warn if people put consumable on non-asset types, because that's redundant.
    syntax Modifier ::= "nonfungible" [token]
                      | "fungible"    [token]
                      | "consumable"  [token]
                      | "asset"       [token]
                      | "copyable"    [token]
    syntax Modifiers ::= List{Modifier, " "}

    syntax TypeQuant ::= "set" [token]
                       | "one" [token]
                       | "option" [token]
                       | "list" [token]
                       | "empty" [token]

    syntax QuantifiedType ::= TypeQuant Type
    syntax BaseType ::= QualifiedId
                      | Type "*" Type
                      | Type "~~>" Type
                      | "(" Type ")" [bracket]
    syntax Type ::= BaseType
                  | QuantifiedType

    syntax VarDef ::= Id ":" Type
    syntax VarDefs ::= List{VarDef, ","}
    syntax TypeDef ::= "type" Id "is" Modifiers Type
    syntax FieldDef ::= VarDef
                      | VarDef ":=" Expr
    syntax TransactionDef ::= "transaction" Id "(" VarDefs ")" "returns" Type ":" Stmt
    syntax Decl ::= TypeDef
                  | TransactionDef
                  | FieldDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | "var" VarDef
                  | "var" VarDef ":=" Expr
                  | "pass" [token]
                  | "return" Expr [strict]
                  | Expr
                  | Stmt Stmt [right]

    // Add the built-in types to the Id sort so we can reference them in the rules
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]
                | "unit"       [token]
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
                   | "any"
                   | "at" "least" "one"

    syntax Flow ::= Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types

    syntax Action ::= "call" Storage "(" Exprs ")"

    syntax TransactionDef ::= "transaction" Id "(" VarDefs ")" ":" Stmt

    // Desugaring
    rule S --> D => S --[ everything ]-> D [macro]

    rule S --[ Sel1 ]-> T:QualifiedId --[ Sel2 ]-> D
         =>
         (S --[ Sel1 ]-> T)
         (T --[ Sel2 ]-> D)
         [macro]

    rule var X : T := E => (var X : T) (E --> X) [macro]

    rule S := E => (S --> consume) (E --> S) [macro]

    rule A > B => B < A [macro]
    rule A >= B => B <= A [macro]
    rule A != B => not (A = B) [macro]

    rule F:Selector not in S => not (F in S) [macro]

    rule exactly one => ! [macro]
    rule any => * [macro]
    rule at least one => + [macro]

    rule transaction T(Args): S
         =>
         transaction T(Args) returns bool: S (return true)
         [macro]
endmodule

