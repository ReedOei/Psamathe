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
                       | Expr "::" Type "~~>" Type
    syntax K ::= Judgement
               | setTypeEnv(Map)
               | assertTypeEnv(Map)

    rule <k> setTypeEnv(M) => . ... </k>
        <typeEnv> Old => M </typeEnv>

    rule <k> assertTypeEnv(M) => . ... </k>
        <typeEnv> M </typeEnv>

    rule <k> S:Stmt => .Map |- S wf </k>

    // Sequence
    rule (S1:Stmt S2:Stmt) wf => S1 wf ~> S2 wf

    // Variable definition
    rule <k> var X : T => . ... </k>
        <typeEnv> ... .Map => X |-> T </typeEnv>

    syntax Type ::= demote(Type) [function]
    rule demote(nat) => nat
    rule demote(bool) => bool
    rule demote(string) => string
    rule demote(address) => address

    // Flow typing
    rule (S --[ Sel ]-> D) wf => S :: ?T1 ~~> ?T2
    rule S :: T1 ~~> T3 =>
        S :: T1 ~~> ?T2
        ~>
        Sel selects demote(T1)
        ~>
        D :: ?T2 ~~> T3
endmodule

