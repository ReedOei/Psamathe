// The syntax module containing the "core" flow language.
module FLOW-CORE-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
                 | "\\" Id ":" Type "." Expr [binder]
    syntax Vals ::= List{Val, ","} [klabel(exprs)]

    syntax QualifiedId ::= Id
                         | Storage "[" Expr "]" [strict(2)]
                         | Storage "." Storage [left]

    syntax Storage ::= Val
                     | QualifiedId
                     | "consume" [token]

    /* syntax TupleExpr ::= "(" Exprs ")" // Tuples *1/ */

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
    syntax Exprs ::= List{Expr, ","} [seqstrict, klabel(exprs)]

    syntax SpecialSelect ::= "everything" [token]
                           | "nothing" [token]
                           // Not sure about this word choice, but it will pick an arbitrary element of
                           | "arbitrary" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "!"
                   | "*"
                   | "+"
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
                            | "transaction" Id "(" VarDefs ")" ":" Stmt
    syntax Decl ::= TypeDef
                  | TransactionDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | "var" VarDef
                  | "var" VarDef ":=" Expr
                  | Stmt Stmt [right]

    // Add the built-in types to the Id sort so we can reference them in the rules
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]

    syntax Contract ::= "contract" Id "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Action ::= "emit" Id "(" Exprs ")"
                    | "error" "(" Expr ")"
                    | "call" Storage "(" Exprs ")"
    syntax Actions ::= List{Action, " "}

    syntax Program ::= Contracts ";" Stmt Actions
endmodule

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX
    imports FLOW-CORE-SYNTAX

    // All the new syntax here gets desugared at some point.
    syntax Expr ::= Expr ">=" Expr [seqstrict]
                  | Expr ">" Expr [seqstrict]
                  | Selector "not" "in" Storage [seqstrict]

    // Quantifiers "speaking names"
    syntax Quant ::= "exactly" "one"
                   | "any"
                   | "at" "least" "one"

    syntax Flow ::= Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types

    syntax Storage ::= "freshStorage" "(" Int ")" [freshGenerator, function, functional, klabel(freshStorage)]

    // Basic desugaring
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

    rule F:Selector not in S => not (F in S) [macro]

    rule exactly one => ! [macro]
    rule any => * [macro]
    rule at least one => + [macro]
endmodule

