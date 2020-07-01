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

    /* syntax Judgement ::= Stmt "wf" */
    /*                    | Expr "selects" Type */
    /*                    | Expr ":" Type */
    /*                    | Flow ":" Type */
    /* syntax K ::= Map "|-" Judgement */

    /* rule <k> S:Stmt => .Map |- S wf </k> */

    /* // Sequence */
    /* rule Gamma |- (S1:Stmt S2:Stmt) wf => Gamma |- S1 wf ~> Gamma |- S2 wf */

    /* // Variable definition */
    /* rule Gamma |- (var X : T in S) wf => Gamma (X |-> T) |- S wf */

    /* syntax Type ::= demote(Type) [function] */
    /* rule demote(nat) => nat */
    /* rule demote(bool) => bool */
    /* rule demote(string) => string */
    /* rule demote(address) => address */

    /* // Flow typing */
    /* rule Gamma |- (S --[ Sel ]-> D) wf => Gamma |- (S --[ Sel ]-> D) : ?T1 ~~> ?T2 */
    /* rule Gamma |- (S --[ Sel ]-> D) : T1 ~~> T3 => */
    /*     Gamma |- S : T1 ~~> ?T2 */
    /*     ~> */
    /*     Gamma |- Sel selects demote(T1) */
    /*     ~> */
    /*     Gamma |- D : ?T2 ~~> T3 */

    /* syntax K ::= nonAsset(Type) */
    /* rule nonAsset(nat) => . */
    /* rule nonAsset(bool) => . */
    /* rule nonAsset(string) => . */
    /* rule nonAsset(address) => . */
    /* rule nonAsset(set T) => nonAsset(T) */
    /* rule nonAsset(list T) => nonAsset(T) */
    /* rule nonAsset(option T) => nonAsset(T) */
    /* rule nonAsset(one T) => nonAsset(T) */
    /* rule nonAsset(T1 * T2) => nonAsset(T1) ~> nonAsset(T2) */
    /* // An empty type is always fine to get rid of. */
    /* rule nonAsset(empty T) => . */

    /* // NOTE: The following rule intentionally commented out so that */
    /* // TODO: Provide a real error message. */
    /* // rule nonAsset(T1 ~~> T2) => . */

    /* rule <k> nonAsset(T:QualifiedId) => nonAsset(Base) </k> */
    /*     <types> ... T |-> modified(Ms, Base) ... </types> */
    /*     requires notBool(asset in Ms) */
endmodule

