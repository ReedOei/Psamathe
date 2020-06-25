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
                  // Comparison operators
                  > Expr "=" Expr [seqstrict]
                  | Expr "!=" Expr [seqstrict]
                  | Expr "<=" Expr [seqstrict]
                  | Expr "<" Expr [seqstrict]
                  | Expr ">=" Expr [seqstrict]
                  | Expr ">" Expr [seqstrict]
                  > Expr "in" Storage [seqstrict]
                  > "not" Expr [strict]
                  > "if" Expr "then" Expr "else" Expr [strict(1)]
    syntax Exprs ::= List{Expr, ","} [seqstrict]

    syntax SpecialSelect ::= "everything" [token]
                           // Not completely sure if "nothing" is useful, but it tends to be useful (at least formally) to have 'no-op's
                           | "nothing" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "exactly" "one"
                   | "!"
                   | "any"
                   | "*"
                   | "at" "least" "one"
                   | "+"
    syntax Selector ::= Expr
                      | SpecialSelect
                      | Quant Id "such" "that" Expr

    syntax Flow ::= Storage
                  | Storage "--[" Selector "]->" Flow [strict(2)]
                  | Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types
                  | "consume" Selector "from" Storage
                  | "consume" Storage

    // Add the built-in types to the Id sort so we can reference them in the rules below
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]

    syntax Stmt ::= Flow
                  | Stmt Stmt [right]

    // Basic desugaring
    rule S --> D => S --[ everything ]-> D [macro]
    rule S --[ Sel1 ]-> T:PersistStorage --[ Sel2 ]-> F
         =>
         (S --[ Sel1 ]-> T)
         (T --[ Sel2 ]-> F) [macro-rec]

    rule X > Y => Y < X   [macro]
    rule X >= Y => Y <= X [macro]
endmodule

module FLOW
    imports FLOW-SYNTAX
    imports DOMAINS
    imports SUBSTITUTION

    syntax KResult ::= Val
                     | Vals
                     | SpecialSelect

    configuration
        <T>
            <k> $PGM:Stmt </k>
            <storage> .Map </storage>
        </T>

    syntax Resource ::= fungible(Id, Int)
                      | nonfungible(Id, Set)

    syntax K ::= split(Selector, Resource, Storage, Storage)
               | flow(Resource, Storage)

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // Simple arithmetic and boolean expressions
    rule I1 + I2 => I1 +Int I2
    rule I1 - I2 => I1 -Int I2

    rule I1:Int = I2:Int => I1 ==Int I2
    rule I1:Int != I2:Int => I1 =/=Int I2

    rule S1:String = S2:String => S1 ==String S2
    rule S1:String != S2:String => S1 =/=String S2

    rule I1 < I2 => I1 <Int I2
    rule I1 <= I2 => I1 <=Int I2

    rule I:Int --[ everything ]-> D => flow(fungible(nat, I), D)
    rule Str:String --[ everything ]-> D => flow(nonfungible(string, SetItem(Str)), D)

    rule <k> S:Storage --[ Sel ]-> D => split(Sel, SV, S, D) ... </k>
        <storage> ...  S |-> SV => .Map ... </storage>

    rule split(everything, fungible(R, V), S, D) => split(V, fungible(R, V), S, D)
    rule split(everything, nonfungible(R, Vals), S, D) => flow(nonfungible(R, .Set), S) ~> flow(nonfungible(R, Vals), D)

    rule split(N:Int, fungible(R, V), S, D) => flow(fungible(R, V -Int N), S) ~> flow(fungible(R, N), D)
        requires V >=Int N

    rule split(Val, nonfungible(R, SetItem(Val) Rest), S, D)
         =>
         flow(nonfungible(R, Rest), S) ~> flow(nonfungible(R, SetItem(Val)), D)

    rule <k> flow(fungible(R, V), S) => . ... </k>
        <storage> ...  S |-> (fungible(R, Cur) => fungible(R, Cur +Int V)) ... </storage>

    rule <k> flow(fungible(R, V), S) => . ... </k>
        <storage> Store => Store S |-> fungible(R, V) </storage>
        requires notBool (S in keys(Store))

    rule <k> flow(nonfungible(R, V), S) => . ... </k>
        <storage> ...  S |-> (nonfungible(R, Cur) => nonfungible(R, Cur V)) ...  </storage>

    rule <k> flow(nonfungible(R, V), S) => . ... </k>
        <storage> Store => Store S |-> nonfungible(R, V) </storage>
        requires notBool (S in keys(Store))
endmodule

