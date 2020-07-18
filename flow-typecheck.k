require "flow-common.k"

module FLOW-TYPECHECK-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-TYPECHECK
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS

    syntax TypeOp ::= Type
    syntax KResult ::= Type
    configuration
        <common />
        <typeEnv> .Map </typeEnv>

    syntax Stmt ::= Selector "selects" "{" TypeQuant "}" Type
                  | Expr ":" Type
                  | Source "provides" "{" TypeQuant "}" Type
                  | Destination "accepts" Type
    // =======================================
    // Boolean Expressions
    // =======================================
    rule (E1 = E2) : ! bool
         =>
         assertEnv(?Gamma) ~>
         E1 : ?Tau ~> assertEnv(?Gamma) ~>
         E2 : ?Tau ~> assertEnv(?Gamma)

    rule (S in X) : ! bool
         =>
         X provides {?_} ?Tau ~>
         S selects {?_} demote(?Tau)

    rule (A and B) : ! bool
         =>
         assertEnv(?Gamma) ~>
         A : ! bool ~> assertEnv(?Gamma) ~>
         B : ! bool ~> assertEnv(?Gamma)

    rule (A or B) : ! bool
         =>
         assertEnv(?Gamma) ~>
         A : ! bool ~> assertEnv(?Gamma) ~>
         B : ! bool ~> assertEnv(?Gamma)

    rule (not A) : ! bool
         =>
         assertEnv(?Gamma) ~> A : ! bool ~> assertEnv(?Gamma)

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
                  | update(Storage, TypeOp)
                  | assertEnv(Map)
                  | setEnv(Map)

    context update(_, HOLE)
    rule <k> update(X, T) => . ... </k>
        <typeEnv> ... X |-> (_ => T) ... </typeEnv>
    rule <k> update(X, _) => . ... </k>
        <typeEnv> Gamma </typeEnv>
        requires notBool(X in keys(Gamma))

    rule <k> insert(X, T) => . ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>

    rule <k> drop(X) => . ... </k>
        <typeEnv> ... X |-> T:Type => .Map ... </typeEnv>
        requires notBool(isAsset(T))

    // Only succeed when the type environment is exactly as expected.
    rule <k> assertEnv(Gamma) => . ... </k>
        <typeEnv> Gamma </typeEnv>

    rule <k> setEnv(Gamma) => . ... </k>
        <typeEnv> _ => Gamma </typeEnv>

    syntax TypeOp ::= typeof(Var)

    rule <k> typeof(X) => typeof(Gamma, X) ... </k>
        <typeEnv> Gamma </typeEnv>

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

    syntax TypeQuant ::= min(TypeQuant, TypeQuant) [function, functional]
                       | max(TypeQuant, TypeQuant) [function, functional]
    rule min(Q, R) => #if Q <Q R #then Q #else R #fi
    rule max(Q, R) => #if Q <Q R #then R #else Q #fi

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

    syntax TypeOp ::= TypeOp "+Ty" TypeQuant
                    | TypeOp "-Ty" TypeQuant

    context HOLE +Ty _
    rule (Q:TypeQuant T) +Ty R => (Q + R) T
    context HOLE -Ty _
    rule (Q:TypeQuant T) -Ty R => (Q - R) T

    // =======================================
    // Type/Type Environment Helpers
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

    syntax TypeQuant ::= join(TypeQuant, TypeQuant) [function, functional]
    rule join(Q:TypeQuant, Q) => Q
    rule join(!, every) => nonempty
    rule join(every, !) => nonempty
    rule join(_:TypeQuant, _:TypeQuant) => any [owise]

    syntax Type ::= join(Type, Type) [function, functional]
    rule join(A, bot) => A
    rule join(bot, B) => B
    rule join(Q:TypeQuant T, R:TypeQuant T) => join(Q, R) T

    syntax Map ::= join(Map, Map) [function, functional]
    rule join(A, .Map) => A
    rule join(.Map, B) => B
    rule join((X |-> T) A, B) => (X |-> join(T, typeof(B, X))) join(A, removeAll(B, SetItem(X)))

    syntax Map ::= restrict(Map, Set) [function, functional]
    rule restrict(M, Ks) => removeAll(M, keys(M) -Set Ks)

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
    // Variable Lookup
    // =======================================
    rule <k> X : demote(T) => . ... </k>
        <typeEnv> ... X |-> T ... </typeEnv>
    rule <k> X : Q T => . ... </k>
        <typeEnv> ... X |-> (Q:TypeQuant T => empty T) ... </typeEnv>

    // =======================================
    // Storage typing
    // =======================================
    rule <k> X accepts (_ T:BaseType) => . ... </k>
        <typeEnv> ... X |-> _ T ... </typeEnv>

    rule <k> X provides {Q} T => . ... </k>
        <typeEnv> ... X |-> Q _:Collection T ... </typeEnv>

    rule <k> X provides {!} T => . ... </k>
        <typeEnv> ... X |-> T ... </typeEnv>

    rule consume accepts T => .
        requires isConsumable(T)

    rule <k> new C.T provides {every} ! T => . </k>
        <typeEnv> ... this |-> C ... </typeEnv>

    // =======================================
    // Selector typing
    // =======================================
    rule everything selects {every} _ => .
    // TODO: Finish

    // =======================================
    // Flow typing
    // =======================================
    // TODO: Implement transformers
    rule S --[ Sel ]-> D =>
        S provides {?Q} ?Tau ~>
        Sel selects {?R} demote(?Tau) ~>
        checkThat(min(?Q, ?R) <Q every) ~>
        update(S, typeof(S) -Ty ?R) ~>
        D accepts ?Tau ~>
        update(D, typeof(D) +Ty min(?Q, ?R))

    // =======================================
    // If Statement
    // =======================================
    rule <k> if E { S1:Stmt } else { S2:Stmt }
             =>
             E : ! bool ~>
             assertEnv(Gamma) ~>
             S1 ~>
             assertEnv(?Delta) ~>
             setEnv(Gamma) ~>
             S2 ~>
             assertEnv(?Xi) ~>
             setEnv(join(?Delta, ?Xi))
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    // =======================================
    // Revert
    // =======================================
    rule <k> revert(E)
             =>
             E : ?Tau ~>
             assertEnv(Gamma)
             ...
         </k>
         <typeEnv> Gamma </typeEnv>
        requires notBool(isAsset(?Tau))

    // =======================================
    // Expression statement
    // =======================================
    rule expr(E) => E : ?Sigma
        requires notBool(isAsset(?Sigma))

    // =======================================
    // Pack
    // =======================================
    rule <k> pack => . ... </k>
        <typeEnv> Gamma => removeAll(Gamma, keys(fieldEnv(Fields))) </typeEnv>
        <fields> ... Gamma[this] |-> Fields </fields>
        requires restrict(Gamma, keys(fieldEnv(Fields))) <=Env fieldEnv(Fields)

    // =======================================
    // Type modifier checking
    // =======================================
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

    // =======================================
    // Misc. helpers
    // =======================================
    syntax Stmt ::= checkEach(Exprs, VarDefs)
    rule checkEach(.Exprs, .VarDefs) => .
    rule checkEach((E, Es):Exprs, (_ : T, Defs)) => E : T ~> checkEach(Es, Defs)

    syntax Stmt ::= checkThat(Bool)
    rule checkThat(true) => .

    // TODO: Maybe just store the fields like this in the first place?
    syntax Map ::= fieldEnv(Set) [function, functional]
    rule fieldEnv(.Set) => .Map
    rule fieldEnv(SetItem(X : T) Rest) => (X |-> T) fieldEnv(Rest)
endmodule

