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
                       | Flow ":" Type
    syntax K ::= Map "|-" Judgement

    rule <k> S:Stmt => .Map |- S wf </k>

    // Sequence
    rule Gamma |- (S1:Stmt S2:Stmt) wf => Gamma |- S1 wf ~> Gamma |- S2 wf

    // Variable definition
    rule Gamma |- (var X : T in S) wf => Gamma (X |-> T) |- S wf

    syntax Type ::= demote(Type) [function]
    rule demote(nat) => nat
    rule demote(bool) => bool
    rule demote(string) => string
    rule demote(address) => address

    // Flow typing
    rule Gamma |- (S --[ Sel ]-> D) wf => Gamma |- (S --[ Sel ]-> D) : ?T1 ~~> ?T2
    rule Gamma |- (S --[ Sel ]-> D) : T1 ~~> T3 =>
        Gamma |- S : T1 ~~> ?T2
        ~>
        Gamma |- Sel selects demote(T1)
        ~>
        Gamma |- D : ?T2 ~~> T3
endmodule

