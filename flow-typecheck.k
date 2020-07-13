require "substitution.k"
require "flow-common.k"

module FLOW-TYPECHECK-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-TYPECHECK
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS
    imports SUBSTITUTION

    syntax KResult ::= Type

    configuration
        <common />
        <typeEnv> .Map </typeEnv>

    syntax Judgement ::= Stmt "wf"
                       | Expr "selects" Type
                       | Expr ":" Type
                       | Storage "::" Type "==>" "{" TypeQuant "}" Type
    syntax K ::= Judgement

    rule <k> S:Stmt => S wf </k>

    // Sequence
    rule (S1:Stmt S2:Stmt) wf => S1 wf ~> S2 wf

    syntax K ::= insert(Map)
               | drop(Set)

    rule <k> insert(M) => . </k>
        <typeEnv> Env => Env M </typeEnv>

    // TODO: Need to check that we actually can drop this stuff
    rule <k> drop(Vars) => . </k>
        <typeEnv> Env => removeAll(Env, Vars) </typeEnv>

    // Variable definition
    rule (var X : T := E) wf => E : T ~> insert(X |-> T)

    // Primitive types
    rule I:Int : ! nat => .
        requires I >=Int 0
    rule B:Bool : ! bool => .
    rule S:String : ! string => .

    // Storage typing
    rule <k> X :: T ==> {Q} T => . ... </k>
        <typeEnv> ... X |-> Q C:Collection T ... </typeEnv>

    // Flow typing
    // TODO: need to update storage information
    rule (S --[ Sel ]-> D) wf =>
        S :: ?T1 ==> {?Q} ?T2 ~>
        Sel selects demote(?T2) ~>
        D :: ?T2 ==> {?R} ?T3

    // Helpers
    syntax Type ::= demote(Type) [function, functional]
    rule demote(Q T:BaseType) => Q demote(T)

    syntax BaseType ::= demote(BaseType) [function, functional]
    rule demote(nat) => nat
    rule demote(bool) => bool
    rule demote(string) => string
    rule demote(address) => address
endmodule

