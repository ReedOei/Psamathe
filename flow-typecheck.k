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
                       | Selector "selects" "{" TypeQuant "}" Type
                       | Expr ":" Type
                       | Storage "::" Type "==>" "{" TypeQuant "}" Type
    syntax K ::= Judgement

    rule <k> S:Stmt => S wf </k>

    // Sequence
    rule (S1:Stmt S2:Stmt) wf => S1 wf ~> S2 wf

    syntax K ::= insert(QualifiedId, Type)
               | drop(QualifiedId)

    rule <k> insert(X, T) => . ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>

    rule <k> drop(X) => nonAsset(T) ... </k>
        <typeEnv> ... X |-> T => .Map ... </typeEnv>

    // Variable definition
    // TODO: Need to change to use the (var X : T := E in S) construct to match the current typing rules
    rule (var X : T := E in S) wf => E : T ~> insert(X, T) ~> S wf ~> drop(X)

    // Primitive types
    rule I:Int : ! nat => .
        requires I >=Int 0
    rule B:Bool : ! bool => .
    rule S:String : ! string => .

    rule emptyval : empty _ => .

    // Storage typing
    rule <k> X :: R T ==> {!} Q T => . ... </k>
        <typeEnv> ... X |-> Q T ... </typeEnv>

    rule <k> X :: T ==> {Q} T => . ... </k>
        <typeEnv> ... X |-> Q C:Collection T ... </typeEnv>

    syntax K ::= checkEach(Exprs, VarDefs)

    rule <k> new C(Args) :: empty void ==> {!} ! C
             =>
             checkEach(Args, ArgDefs)
             ...  </k>
        <constructors> ... C |-> constructor(ArgDefs, _) ... </constructors>

    rule consume :: T ==> {empty} empty void
         =>
         checkConsumable(T)

    rule checkEach(.Exprs, .VarDefs) => .
    rule checkEach((E, Es):Exprs, (_ : T, Defs)) => E : T ~> checkEach(Es, Defs)

    // Selector typing
    rule everything selects {every} T => .

    // Flow typing
    // TODO: need to update storage information
    rule (S --[ Sel ]-> D) wf =>
        S :: ?T1 ==> {?Q} ?T2 ~>
        Sel selects {?R} demote(?T2) ~>
        D :: ?T2 ==> {?_} ?T3

    // Type modifier checking
    syntax K ::= checkConsumable(Type)
               | checkConsumable(BaseType)
               | nonAsset(Type)

    /* rule checkConsumable(Q:TypeQuant T) => nonAsset(Q T) or checkConsumable(T) */
    /*     <types> ... T |-> modified(Ms, _) ... </types> */
    /*     requires consumable in Ms */
endmodule

