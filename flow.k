require "substitution.k"

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax TxResult ::= "success" [token]
                      | failure(Id, String)

    syntax Val ::= Int
                 | Bool
                 | String
                 | TxResult

    syntax Storage ::= Id
                     | Int
                     | Storage "[" Expr "]"     [strict(2)]

    syntax Expr ::= Val
                  | Storage
                  | "(" Expr ")"        [bracket]
                  | "if" Expr "then" Expr "else" Expr [strict(1)]
                  | Expr "+" Expr [strict]
                  | Expr "-" Expr [strict]
                  > Expr "=" Expr [strict]
                  | Expr "<=" Expr [strict]
                  | Expr "<" Expr [strict]

    syntax Everything ::= "everything" [token]
    syntax Selector ::= Expr
                      | Everything

    syntax Flow ::= Storage "---" Selector "-->" Storage [strict(2)]
                  | Storage "-->" Storage
                  | Storage "+=" Expr
                  | "consume" Selector "from" Storage
                  | "consume" Storage

    syntax VarDef ::= Id ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax Stmt ::= Flow
                  | VarDef
                  | Storage ":=" Expr
                  | Stmt Stmt [right]

    // Add the built-in types to the Id sort so we can reference them in the rules below
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]

    syntax Type ::= Id
                  | "(" Type ")" [bracket]
                  | "map" Type "=>" Type
                  | "linking" Type "---" "{" Type "}"
                  | "set" Type
                  | "option" Type
                  | "{" VarDefs "}"

    syntax Modifier ::= "nonfungible" [token]
                      | "fungible"    [token]
                      | "consumable"  [token]
                      | "asset"       [token]
    syntax Modifiers ::= List{Modifier, " "}
    syntax TypeDef ::= "type" Id "is" Modifier Type
    syntax TypeDefs ::= List{TypeDef, " "}

    syntax Transaction ::= "transaction" Id "(" VarDefs ")" ":" Stmt
                         | "transaction" Id "(" VarDefs ")" "returns" Type ":" Stmt
                         | "view" Id "(" VarDefs ")" returns Type ":=" Expr
    syntax Transactions ::= List{Transaction, " "}

    syntax Decl ::= TypeDef
                  | VarDef
                  | Transaction

    syntax Contract ::= "contract" Id "{" TypeDefs Transactions "}"
    syntax Contracts ::= List{Contract, " "}
    syntax Program ::= Contracts Stmt

    // Basic desugaring
    rule S --> D => S --- everything --> D [macro]
endmodule

module FLOW
    imports FLOW-SYNTAX
    imports DOMAINS
    imports SUBSTITUTION

    syntax KResult ::= Val
                     | Everything

    configuration
        <T>
            <k> $PGM:Program </k>
            <storage> .Map </storage>
        </T>

    syntax Resource ::= fungible(Id, Int)
                      | nonfungible(Id, Set)

    syntax K ::= split(Selector, Resource, Storage, Storage)
               | flow(Resource, Storage)

    rule .Contracts S:Stmt => S

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // Standard lookup rule
    rule
        <k> Var:Id => Val ... </k>
        <storage> ... Var |-> Val ...  </storage>

    // A dummy storage location, for use with constants
    syntax Storage ::= "#null" [token]

    rule I:Int --- Sel --> D => split(Sel, fungible(nat, I), #null, D)
    rule
        <k> S:Storage --- Sel --> D => split(Sel, SV, S, D) ... </k>
        <storage>
            ...
            S |-> SV
            =>
            .Map
            ...
        </storage>

    rule split(everything, fungible(R, V), S, D) => split(V, fungible(R, V), S, D)
    // TODO
    /* rule split(everything, nonfungible(R, Vals), S, D) => split(Vals, nonfungible(R, Vals), S, D) */

    rule split(N:Int, fungible(R, V), S, D) => flow(fungible(R, V -Int N), S) ~> flow(fungible(R, N), D)
        requires V >=Int N

    rule split(Val, nonfungible(R, SetItem(Val) Rest), S, D)
         =>
         flow(nonfungible(R, Rest), S) ~> flow(nonfungible(R, SetItem(Val)), D)

    rule
        <k> flow(fungible(R, V), S) => . ... </k>
        <storage>
            ...
            S |-> (fungible(R, Cur) => fungible(R, Cur +Int V))
            ...
        </storage>

    rule
        <k> flow(fungible(R, V), S) => . ... </k>
        <storage>
            Store
            =>
            Store
            S |-> fungible(R, V)
        </storage>
        requires notBool (S in keys(Store))

    rule
        <k> flow(nonfungible(R, V), S) => . ... </k>
        <storage>
            ...
            S |-> (nonfungible(R, Cur) => nonfungible(R, Cur V))
            ...
        </storage>

    rule
        <k> flow(nonfungible(R, V), S) => . ... </k>
        <storage>
            Store
            =>
            Store
            S |-> nonfungible(R, V)
        </storage>
        requires notBool (S in keys(Store))

endmodule

