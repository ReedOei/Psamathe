require "substitution.k"

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax TxResult ::= "success" [token]
                      | failure(String)

    syntax Val ::= Int
                 | Bool
                 | String
                 | TxResult

    syntax Storage ::= Id
                     | Storage "[" Expr "]"     [strict(2)]

    syntax Expr ::= Val
                  | "(" Expr ")"        [bracket]
                  | Storage

    syntax Everything ::= "everything" [token]
    syntax Selector ::= Expr
                      | Everything

    syntax Flow ::= Expr "---" Selector "-->" Expr [strict(2)]
                  | Expr "-->" Expr
                  | Expr "+=" Expr

    syntax Stmt ::= Flow
                  | Stmt Stmt [right]

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
            <k> $PGM:Stmt </k>
            <storage> .Map </storage>
        </T>

    syntax Resource ::= fungible(String, Int)
                      | nonfungible(String, Set)

    syntax K ::= split(Selector, Resource, Storage, Storage)

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // Linear lookup, removes value from the store.
    rule
        <k> Var:Id => Val ... </k>
        <storage>
            ... Var |-> Val => .Map ...
        </storage>

    // A dummy storage location
    syntax Storage ::= "#null" [token]

    rule I:Int --- Sel --> D => split(Sel, fungible("nat", I), #null, D)
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

    rule
        <k> split(N:Int, fungible(R, V), S, D) => . ... </k>
        <storage>
            Store
            =>
            Store
            S |-> fungible(R, V -Int N)
            D |-> fungible(R, N)
        </storage>
        requires V >=Int N
        requires not (D in keys(Store))

    rule
        <k> split(Val:String, nonfungible(R, SetItem(Val) Rest), S, D) => . ... </k>
        <storage>
            Store
            =>
            Store
            S |-> nonfungible(R, Rest)
            D |-> nonfungible(R, SetItem(Val))
        </storage>
        requires not (D in keys(Store))
endmodule

