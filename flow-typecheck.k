require "flow-common.k"

module FLOW-TYPECHECK-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-TYPECHECK
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS

    syntax KResult ::= Type

    configuration
        <common />
        <typeEnv> .Map </typeEnv>


    syntax K ::= Stmt "wf"
               | Selector "selects" "{" TypeQuant "}" Type
               | Expr ":" Type
               | Source "provides" "{" TypeQuant "}" Type
               | Destination "accepts" Type

    rule <k> S:Stmt => S wf </k>

    // Sequence
    rule (S1:Stmt S2:Stmt) wf => S1 wf ~> S2 wf

    syntax K ::= insert(Var, Type)
               | drop(Var)

    rule <k> insert(X, T) => . ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>

    rule <k> drop(X) => . ... </k>
        <typeEnv> ... X |-> T:Type => .Map ... </typeEnv>
        requires notBool(isAsset(T))

    // Variable definition
    // TODO: Need to change to use the (var X : T := E in S) construct to match the current typing rules
    rule (var X : T := E in S) wf => E : T ~> insert(X, T) ~> S wf ~> drop(X)

    // Primitive types
    rule I:Int : ! nat => .
        requires I >=Int 0
    rule _:Bool : ! bool => .
    rule _:String : ! string => .

    rule emptyval : empty _ => .

    // Storage typing
    rule <k> X accepts (_ T:BaseType) => . ... </k>
        <typeEnv> ... X |-> _ T ... </typeEnv>

    rule <k> X provides {Q} T => . ... </k>
        <typeEnv> ... X |-> Q _:Collection T ... </typeEnv>

    rule <k> X provides {!} T => . ... </k>
        <typeEnv> ... X |-> T ... </typeEnv>

    syntax K ::= checkEach(Exprs, VarDefs)

    rule consume accepts T => .
        requires isConsumable(T)

    rule checkEach(.Exprs, .VarDefs) => .
    rule checkEach((E, Es):Exprs, (_ : T, Defs)) => E : T ~> checkEach(Es, Defs)

    // Selector typing
    rule everything selects {every} _ => .

    // Flow typing
    // TODO: need to update storage information
    rule (S --[ Sel ]-> D) wf =>
        S provides {?Q} ?T1 ~>
        Sel selects {?R} demote(?T1) ~>
        D accepts ?T1

    // Type modifier checking
    syntax Bool ::= isConsumable(Type) [function, functional]
               | isConsumable(BaseType) [function, functional]
               | isAsset(Type) [function, functional]
               | isAsset(BaseType) [function, functional]

    syntax Set ::= modifiers(BaseType) [function, functional]

    rule [[ modifiers(T) => Ms ]]
        <types> ... T |-> modified(Ms, _) ... </types>
    rule [[ modifiers(T) => .Set ]]
        <types> Types </types>
        requires notBool(T in keys(Types))

    // TODO: Finish this definition
    rule isAsset(Q:TypeQuant T) => Q =/=K empty andBool (notBool(asset in modifiers(T)))
endmodule

