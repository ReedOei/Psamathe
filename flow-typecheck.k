require "flow-common.k"

module FLOW-TYPECHECK-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-TYPECHECK
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS

    syntax KResult
    configuration
        <common />
        <typeEnv> .Map </typeEnv>

    syntax Stmt ::= Selector "selects" "{" TypeQuant "}" Type
                  | Expr ":" Type
                  | Source "provides" "{" TypeQuant "}" Type
                  | Destination "accepts" Type

    // =======================================
    // Pass
    // =======================================
    rule pass => .

    // =======================================
    // Sequence
    // =======================================
    rule (S1:Stmt S2:Stmt) => S1 ~> S2

    // =======================================
    // Type Environment Manipulation
    // =======================================
    syntax Stmt ::= insert(Var, Type)
                  | drop(Var)
                  | update(Storage, Type)

    rule <k> update(X, T) => . </k>
        <typeEnv> ... X |-> (_ => T) ... </typeEnv>
    rule <k> update(X, _) => . </k>
        <typeEnv> Gamma </typeEnv>
        requires notBool(X in keys(Gamma))

    rule <k> insert(X, T) => . ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>

    rule <k> drop(X) => . ... </k>
        <typeEnv> ... X |-> T:Type => .Map ... </typeEnv>
        requires notBool(isAsset(T))

    syntax Type ::= typeof(Map, Var) [function, functional]

    // Bottom
    syntax Type ::= "bot"

    rule typeof((X |-> T) _, X) => T
    rule typeof(Gamma, X) => bot
        requires notBool(X in keys(Gamma))

    // =======================================
    // Type Quantity Operators
    // =======================================
    syntax Bool ::= TypeQuant "<Q" TypeQuant [function, functional]
                  | TypeQuant "<=Q" TypeQuant [function, functional]
    rule empty <Q Q => Q =/=K empty
    rule any <Q ! => true
    rule any <Q nonempty => true
    rule any <Q every => true
    rule ! <Q nonempty => true
    rule ! <Q every => true
    rule nonempty <Q every => true
    rule _ <Q _ => false [owise]

    rule Q <=Q R => Q <Q R orBool Q ==K R

    syntax TypeQuant ::= TypeQuant "+" TypeQuant [function, functional]
                       | TypeQuant "-" TypeQuant [function, functional]

    rule Q + empty => Q
    rule _ + every => every
    rule nonempty + R => nonempty requires empty <Q R andBool R <Q every
    rule ! + R => nonempty requires empty <Q R andBool R <Q every
    rule any + any => any

    rule Q - empty => Q
    rule empty - _ => empty
    rule _ - every => empty
    rule every - R => every requires R <Q every
    rule nonempty - R => any requires empty <Q R andBool R <Q every
    rule ! - R => empty requires ! <=Q R
    rule ! - any => any
    rule any - R => any requires empty <Q R andBool R <Q every

    // =======================================
    // Type/Type Environment Ordering
    // =======================================
    syntax Bool ::= TypeQuant "[" TypeQuant [function, functional]
                  | TypeQuant "[=" TypeQuant [function, functional]
                  | Type "<=Ty" Type [function, functional]
                  | Map "<=Env" Map [function, functional]
    rule Q [ R => (Q =/=K any andBool R ==K any) orBool (Q in (SetItem(!) SetItem(every)) andBool R ==K nonempty)
    rule Q [= R => Q [ R orBool Q ==K R
    rule Q:TypeQuant TQ <=Ty R:TypeQuant TR => (TQ ==K TR) andBool (Q [= R)
    rule .Map <=Env _ => true
    rule ((X |-> T) As) <=Env B => (typeof(B, X) <=Ty T) andBool As <=Env B

    // =======================================
    // Primitive types
    // =======================================
    rule I:Int : ! nat => .
        requires I >=Int 0
    rule _:Bool : ! bool => .
    rule _:String : ! string => .

    rule emptyval : empty _ => .

    // =======================================
    // Variable definition
    // =======================================
    rule var X : T := E in S:Stmt => E : T ~> insert(X, T) ~> S ~> drop(X)

    // =======================================
    // New contract
    // =======================================
    rule <k> new C(Args) : ! C => checkEach(Args, FormalArgs) ... </k>
        <constructors> ... C |-> constructor(FormalArgs, _) ... </constructors>

    // =======================================
    // Storage typing
    // =======================================
    rule <k> X accepts (_ T:BaseType) => . ... </k>
        <typeEnv> ... X |-> _ T ... </typeEnv>

    rule <k> X provides {Q} T => . ... </k>
        <typeEnv> ... X |-> Q _:Collection T ... </typeEnv>

    rule <k> X provides {!} T => . ... </k>
        <typeEnv> ... X |-> T ... </typeEnv>

    syntax Stmt ::= checkEach(Exprs, VarDefs)

    // =======================================
    // Consume typing
    // =======================================
    rule consume accepts T => .
        requires isConsumable(T)

    rule checkEach(.Exprs, .VarDefs) => .
    rule checkEach((E, Es):Exprs, (_ : T, Defs)) => E : T ~> checkEach(Es, Defs)

    // =======================================
    // Selector typing
    // =======================================
    rule everything selects {every} _ => .

    // =======================================
    // Flow typing
    // =======================================
    // TODO: need to update storage information
    rule S --[ Sel ]-> D =>
        S provides {?Q} ?T1 ~>
        Sel selects {?R} demote(?T1) ~>
        D accepts ?T1

    /* // Type modifier checking */
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
    rule isAsset(Q:TypeQuant T) => Q =/=K empty andBool (asset in modifiers(T))

    rule isConsumable(Q:TypeQuant T) => (consumable in modifiers(T)) orBool notBool(isAsset(Q T))
endmodule

