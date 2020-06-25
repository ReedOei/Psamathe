require "substitution.k"

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
                 | "transformer" "(" "\\" Id "|->" Expr ")"
    syntax Vals ::= List{Val, ","} [klabel(vals)]
    syntax Ids ::= List{Id, ","} [klabel(vals)]

    syntax PersistStorage ::= Id
                            | Storage "[" Expr "]"     [strict(2)]
    syntax Storage ::= PersistStorage
                     | Val

    syntax Expr ::= Storage
                  | "(" Expr ")"        [bracket]
                  // Set literals
                  | "{" Exprs "}"
                  // Link literal
                  | Expr "<=>" Expr
                  | Id "(" Exprs ")"
                  > Expr "or" Expr [strict(1)]
                  | Expr "and" Expr [strict(1)]
                  > Expr "+" Expr [left, seqstrict]
                  | Expr "-" Expr [left, seqstrict]
                  > Expr "=" Expr [seqstrict]
                  | Expr "<=" Expr [seqstrict]
                  | Expr "<" Expr [seqstrict]
                  | Expr ">=" Expr [seqstrict]
                  | Expr ">" Expr [seqstrict]
                  > Expr "in" Storage [seqstrict]
                  > "not" Expr [strict]
                  > "if" Expr "then" Expr "else" Expr [strict(1)]
    syntax Exprs ::= List{Expr, ","} [seqstrict]

    syntax Everything ::= "everything" [token]
                        // Not sure if "nothing" is useful, but it tends to be useful, at least formally, to have 'no-op' operations.
                        | "nothing" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "exactly" "one"
                   | "!"
                   | "any"
                   | "*"
                   | "at" "least" "one"
                   | "+"
    syntax Selector ::= Expr
                      | Everything
                      | Quant Id "such" "that" Expr

    syntax Flow ::= Storage
                  | Storage "--[" Selector "]->" Flow [strict(2)]
                  | Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types
                  | "consume" Selector "from" Storage
                  | "consume" Storage


    // Basic desugaring
    rule S --> D => S --[ everything ]-> D [macro]
endmodule

module FLOW
    imports FLOW-SYNTAX
    imports DOMAINS
    imports SUBSTITUTION

    configuration
        <T>
            <k> $PGM:Program </k>
            <storage> .Map </storage>
        </T>
endmodule

