require "substitution.k"

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
                 | "\\" Id "." Expr [binder]
    syntax Vals ::= List{Val, ","} [klabel(vals)]

    syntax Storage ::= Val
                     | Id
                     | Storage "[" Expr "]" [strict(2)]
                     | Storage "." Storage [left]

    syntax Expr ::= Storage
                  | "(" Expr ")"        [bracket]
                  | "{" Exprs "}" // Set literals
                  | Expr "<=>" Expr // Link literal
                  | "(" Exprs ")" // Tuples
                  | Id "(" Exprs ")" // Function call (can only call views)
                  > Expr "or" Expr [strict(1)]
                  | Expr "and" Expr [strict(1)]
                  > Expr "+" Expr [left, seqstrict]
                  | Expr "-" Expr [left, seqstrict]
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
                      | Quant Id "such" "that" Expr [binder]

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

    syntax Modifier ::= "nonfungible" [token]
                      | "fungible"    [token]
                      | "consumable"  [token]
                      | "asset"       [token]
    syntax Modifiers ::= List{Modifier, " "}

    syntax Type ::= Id

    syntax TypeDef ::= "type" Id "is" Modifiers Type
    syntax Decl ::= TypeDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | Stmt Stmt [right]

    syntax Contract ::= "contract" Id "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Program ::= Contracts ";" Stmt

    // Basic desugaring
    rule S --> D => S --[ everything ]-> D [macro]

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
            <k> $PGM:Program </k>
            <storage> .Map </storage>
            <contracts> .Map </contracts>
            <types> .Map </types>
        </T>

    // Helper terms
    syntax TypeName ::= Id
                      | qualified(Id, TypeName)

    syntax TypeMod ::= modified(Set, Type)

    syntax Resource ::= fungible(TypeName, Int)
                      | nonfungible(TypeName, Set)

    syntax K ::= split(Selector, Resource, Storage, Flow)
               | flow(Resource, Flow)
               | processDecls(Id, Decls)

    syntax KItem ::= TypeName
                   | TypeMod

    rule <k> contract C { Ds } Cs ; S => processDecls(C, Ds) ~> Cs ; S ... </k>
        <contracts> ... .Map => C |-> contract C { Ds } ... </contracts>
    rule .Contracts ; S => S [structural]

    syntax Set ::= modToSet(Modifiers) [function]
    rule modToSet(.Modifiers) => .Set
    rule modToSet(M:Modifier Ms) => SetItem(M) modToSet(Ms)

    rule <k> processDecls(C, (type T is Mods BaseType) Ds) => processDecls(C, Ds) ... </k>
        <types> ... .Map => qualified(C, T) |-> modified(modToSet(Mods), BaseType) ... </types>
    rule processDecls(C, .Decls) => .

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

    rule <k> S --[ Sel ]-> D => flow(SV, S --[ Sel ]-> D) ... </k>
         <storage> ...  S |-> SV => .Map ... </storage>

    rule split(everything, fungible(R, V), S, D) => split(V, fungible(R, V), S, D)
    rule split(everything, nonfungible(R, Vals), S, D) => flow(nonfungible(R, .Set), S) ~> flow(nonfungible(R, Vals), D)

    rule split(N:Int, fungible(R, V), S, D) => flow(fungible(R, V -Int N), S) ~> flow(fungible(R, N), D)
        requires V >=Int N

    rule split(Val, nonfungible(R, SetItem(Val) Rest), S, D)
         =>
         flow(nonfungible(R, Rest), S) ~> flow(nonfungible(R, SetItem(Val)), D)

    rule flow(R, S --[ Sel ]-> D) => split(Sel, R, S, D)

    rule <k> flow(fungible(R, V), S:Storage) => . ... </k>
        <storage> ...  S |-> (fungible(R, Cur) => fungible(R, Cur +Int V)) ... </storage>

    rule <k> flow(fungible(R, V), S:Storage) => . ... </k>
        <storage> Store => Store S |-> fungible(R, V) </storage>
        requires notBool (S in keys(Store))

    rule <k> flow(nonfungible(R, V), S:Storage) => . ... </k>
        <storage> ...  S |-> (nonfungible(R, Cur) => nonfungible(R, Cur V)) ...  </storage>

    rule <k> flow(nonfungible(R, V), S:Storage) => . ... </k>
        <storage> Store => Store S |-> nonfungible(R, V) </storage>
        requires notBool (S in keys(Store))

    // TODO: Need to check that SV is consumable
    rule <k> consume S => . ... </k>
        <storage> ... S |-> SV => .Map ... </storage>

    syntax Storage ::= "freshStorage" "(" Int ")" [freshGenerator, function, functional, klabel(freshStorage)]

    rule consume V from S => S --[ V ]-> !Fresh ~> consume !Fresh
endmodule

