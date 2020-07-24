require "flow-common.k"

module FLOW-TYPECHECK-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-TYPECHECK
    imports FLOW-TYPECHECK-SYNTAX
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

    rule <k> execute ~> S => contractsOk(Cs) ~> S </k>
        <contracts> Cs </contracts>

    // =======================================
    // Ok-ness checking
    // =======================================
    syntax Stmt ::= contractsOk(Set)
                  | contractOk(Var)
                  | fieldOk(VarDef)

    rule contractsOk(.Set) => .
    rule contractsOk(SetItem(C) Rest) => contractOk(C) ~> contractsOk(Rest)

    // TODO: FINISH THIS
    rule contractOk(C) => .

    // =======================================
    // Type Errors
    // =======================================
    syntax TypeError ::= typeError(Stmt)
    syntax Stmt ::= TypeError

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
    // Let Expr
    // TODO: Maybe unify this with the var ... in S Statement because they're basically the same. Could use a form where we only have expressions, and no statements.
    // =======================================
    rule (let X : T := E in Body) : Tau => E : T ~> insert(X, T) ~> Body : Tau ~> drop(X)

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
                  | assertPartialEnv(Map)
                  | setEnv(Map)

    context update(_, HOLE)
    rule <k> update(X, T:Type) => . ... </k>
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

    rule <k> assertPartialEnv(Gamma) => . ... </k>
        <typeEnv> _ Gamma </typeEnv>

    rule <k> setEnv(Gamma) => . ... </k>
        <typeEnv> _ => Gamma </typeEnv>

    syntax TypeOp ::= typeof(Storage)

    rule <k> typeof(X) => typeof(Gamma, X) ... </k>
        <typeEnv> Gamma </typeEnv>
    rule typeof(new _) => bot
    rule typeof(consume) => bot

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
    rule bot +Ty _ => bot
    context HOLE -Ty _
    rule (Q:TypeQuant T) -Ty R => (Q - R) T
    rule bot -Ty _ => bot

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

    rule I:Int : T => typeError(I : T)
        requires T =/=K (! nat) orBool I <Int 0

    rule _:Bool : ! bool => .
    rule B:Bool : T => typeError(B : T)
        requires T =/=K (! bool)

    rule _:String : ! string => .
    rule S:String : T => typeError(S : T)
        requires T =/=K (! string)

    rule emptyval : empty _ => .
    rule emptyval : Q:TypeQuant T => typeError(emptyval : Q T)
        requires Q =/=K empty

    // =======================================
    // Variable definition
    // =======================================
    rule var X : T := E in S:Stmt => E : T ~> insert(X, T) ~> S ~> drop(X)

    // =======================================
    // New contract
    // =======================================
    rule <k> new C(Args) : ! C => checkEach(Args, FormalArgs) ... </k>
        <constructors> ... C |-> constructor(FormalArgs, _) ... </constructors>

    rule new C(Args) : T => typeError(new C(Args) : T)
        requires T =/=K (! C)

    // =======================================
    // Variable Lookup
    // =======================================
    rule <k> X : demote(T) => . ... </k>
        <typeEnv> ... X |-> T ... </typeEnv>

    // There's no reason to use this rule if the type isn't an asset, because demote will always give us something equivalent to T
    rule <k> X : Q T => . ... </k>
        <typeEnv> ... X |-> (Q:TypeQuant T => empty T) ... </typeEnv>
        requires isAsset(Q T)

    rule <k> X : T:Type => typeError(X : T) ... </k>
        <typeEnv> ... X |-> S:Type ... </typeEnv>
        requires (demote(S) =/=K T)
         andBool (notBool(isAsset(T)) orBool S =/=K T)

    // =======================================
    // Storage typing
    // =======================================
    syntax Type ::= elemtype(BaseType) [function, functional]

    rule elemtype(_:Collection T) => T
    rule elemtype(T) => ! T [owise]

    rule <k> X accepts elemtype(T) => . ... </k>
        <typeEnv> ... X |-> _:TypeQuant T ... </typeEnv>

    rule consume accepts T => .
        requires isConsumable(T)

    rule <k> X provides {Q} elemtype(T) => . ... </k>
        <typeEnv> ... X |-> Q:TypeQuant T ... </typeEnv>

    rule <k> new C.T provides {every} ! T => . </k>
        <typeEnv> ... this |-> C ... </typeEnv>

    // =======================================
    // Selector typing
    // =======================================
    rule everything selects {every} _ => .

    rule E:Expr selects {Q} T => assertEnv(?Gamma) ~> E : Q ?T2 ~> assertEnv(?Gamma) ~> typeEq(elemtype(?T2), T)

    rule (Q X : T such that E) selects {Q} T =>
        assertEnv(?Gamma) ~>
        insert(X, T) ~> E : ! bool ~> drop(X) ~>
        assertEnv(?Gamma)

    // =======================================
    // Flow typing
    // =======================================
    // TODO: Implement transformers
    // TODO: Deal with any potential ambiguities
    rule S --[ Sel ]-> D =>
        S provides {?Q} ?Tau ~>
        Sel selects {?R} demote(?Tau) ~>
        // TODO: Update this to the newer version in the rules.
        checkThat(min(?Q, ?R) <Q every) ~>
        update(S, typeof(S) -Ty ?R)
        D accepts ?Tau ~>
        update(D, typeof(D) +Ty min(?Q, ?R))

    // =======================================
    // If Statement, Expr
    // =======================================
    rule if E { S1:Stmt } else { S2:Stmt }
         =>
         assertEnv(?Gamma) ~>
         E : ! bool ~> assertEnv(?Gamma) ~>
         S1 ~> assertEnv(?Delta) ~>
         setEnv(?Gamma) ~>
         S2 ~> assertEnv(?Xi) ~>
         setEnv(join(?Delta, ?Xi))

    rule (if E { E1 } else { E2 }) : Tau
         =>
         assertEnv(?Gamma) ~>
         E : ! bool ~> assertEnv(?Gamma) ~>
         E1 : Tau ~> assertEnv(?Delta) ~>
         setEnv(?Gamma) ~>
         E2 : Tau ~> assertEnv(?Xi) ~>
         setEnv(join(?Delta, ?Xi))

    // =======================================
    // Try-Catch
    // =======================================
    rule try { S1 } catch (X : T) { S2 }
         =>
         assertEnv(?Gamma) ~>
         S1 ~> assertEnv(?Delta) ~>
         setEnv(?Gamma) ~>
         insert(X, T) ~> S2 ~> drop(X) ~> assertEnv(?Xi) ~>
         setEnv(join(?Delta, ?Xi))

    // =======================================
    // Revert
    // =======================================
    rule revert(E)
         =>
         assertEnv(?Gamma) ~>
         E : ?Tau ~>
         checkThat(notBool(isAsset(?Tau))) ~>
         assertEnv(?Gamma)

    // =======================================
    // Expression statement
    // =======================================
    rule expr(E) => E : ?Sigma ~> checkThat(notBool(isAsset(?Sigma)))

    // =======================================
    // View calls
    // =======================================
    rule <k> X.F(Args) : T => checkEach(Args, FormalArgs) ... </k>
         <typeEnv> ... X |-> (! C) ... </typeEnv>
         <functions> ... C |-> (SetItem(view(F, T, FormalArgs, _)) _) ... </functions>

    // =======================================
    // Internal calls
    // =======================================
    rule <k> this.F(Args) : T => packed(C) ~> checkEach(Args, FormalArgs) ~> assertPartialEnv(this |-> C) ... </k>
        <typeEnv> ... this |-> (! C) ... </typeEnv>
        <functions> ... C |-> (SetItem(transaction(F, _ : T, FormalArgs, _)) _) ... </functions>

    syntax Stmt ::= packed(Var)

    // =======================================
    // External calls
    // =======================================

    // =======================================
    // Unpack
    // =======================================
    rule <k> unpack(F) => . ... </k>
        <typeEnv> Gamma (this |-> (! C)) (.Map => this.F |-> T) </typeEnv>
        <fields> ... C |-> (SetItem((F : T):VarDef) _) ... </fields>
        requires notBool(this.F in keys(Gamma))

    // =======================================
    // Pack
    // =======================================
    rule <k> pack => . ... </k>
        <typeEnv> ((this |-> (! C)) _) #as Gamma => removeAll(Gamma, keys(fieldEnv(Fields))) </typeEnv>
        <fields> ... C |-> Fields </fields>
        requires restrict(Gamma, keys(fieldEnv(Fields))) <=Env fieldEnv(Fields)

    syntax Stmt ::= packed(Var)
    rule <k> packed(C) => . ... </k>
        <typeEnv> Gamma </typeEnv>
        <fields> C |-> Fields </fields>
        requires intersectSet(keys(Fields), keys(Gamma)) ==K .Set

    // =======================================
    // Type modifier checking
    // =======================================
    syntax Bool ::= isConsumable(Type) [function, functional]
                  | isConsumable(BaseType) [function, functional]
                  | isAsset(Type) [function, functional]
                  | isAsset(BaseType) [function, functional]

    syntax Set ::= modifiers(BaseType) [function, functional]

    rule [[ modifiers(C.T) => Ms ]]
        <types> ... C |-> (SetItem(type(T, Ms, _)) _) ... </types>
    rule [[ modifiers(T) => Ms ]]
        <types> ... T |-> (SetItem(type(T, Ms, _)) _) ... </types>

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

    syntax Stmt ::= typeEq(Type, Type)
    rule typeEq(T, T) => .

    // TODO: Maybe just store the fields like this in the first place?
    syntax Map ::= fieldEnv(Set) [function, functional]
    rule fieldEnv(.Set) => .Map
    rule fieldEnv(SetItem(X : T) Rest) => (X |-> T) fieldEnv(Rest)
endmodule

