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
        [structural]

    // =======================================
    // Ok-ness checking
    // =======================================
    // NOTE: This section could be a HUGE source of nondeterminism (because of all the sets) if the K framework doesn't handle structural as I expect.
    //       Check on this for performance issues.
    syntax Stmt ::= contractsOk(Set)
                  | contractOk(Var)

    rule contractsOk(.Set) => . [structural]
    rule contractsOk(SetItem(C) Rest) => contractOk(C) ~> contractsOk(Rest) [structural]

    // TODO: Need to ensure that we have a unique constructor and check that too.
    rule <k> contractOk(C) => fieldsOk(C, Fields) ~> typesOk(C, Types) ~> functionsOk(C, Funcs) ... </k>
        <fields> ... C |-> fields(Fields) ... </fields>
        <types> ... C |-> types(Types) ... </types>
        <functions> ... C |-> functions(Funcs) ... </functions>

    syntax Stmt ::= fieldsOk(Var, Map)
                  | fieldOk(Var, Type)

    rule fieldsOk(_, .Map) => . [structural]
    rule fieldsOk(C, (_ |-> T) Rest) => fieldOk(C, T) ~> fieldsOk(C, Rest) [structural]

    // TODO: Finish
    rule fieldOk(_, _) => .

    syntax Stmt ::= typesOk(Var, Map)
                  | typeOk(Var, TypeData)

    rule typesOk(_, .Map) => . [structural]
    rule typesOk(C, (_ |-> TDef) Rest) => typeOk(C, TDef) ~> typesOk(C, Rest) [structural]

    // TODO: Finish encoding the various constraints
    rule typeOk(_, type(Ms, BaseT)) => .
        requires (notBool(consumable in Ms) orBool (asset in Ms))
         andBool (notBool(isAsset(BaseT)) orBool (asset in Ms))

    syntax Stmt ::= functionsOk(Var, Map)
                  | functionOk(Var, FuncData)

    rule functionsOk(_, .Map) => . [structural]
    rule functionsOk(C, (_ |-> Func) Rest) => functionOk(C, Func) ~> functionsOk(C, Rest) [structural]

    rule functionOk(C, view(RetType, Args, Body))
         =>
         setEnv((this |-> (! C)) makeEnv(varDefsToSet(Args)) fieldsOf(C)) ~>
         assertEnv(?Gamma) ~> Body : RetType ~> assertEnv(?Gamma) ~>
         setEnv(.Map)

    rule functionOk(C, transaction(RetVar : Q:TypeQuant RetType, Args, Body))
         =>
         setEnv((this |-> (! C)) (RetVar |-> (empty RetType)) makeEnv(varDefsToSet(Args))) ~>
         Body ~>
         assertEnv((this |-> (! C)) (RetVar |-> (Q RetType)) ?Rest) ~>
         checkThat(notBool(isAsset(Q RetType))) ~>
         packed ~>
         allNonAsset(?Rest) ~>
         setEnv(.Map)

    // =======================================
    // Type Errors
    // =======================================
    syntax TypeError ::= typeError(Stmt)
    syntax Stmt ::= TypeError

    // =======================================
    // Boolean Expressions
    // =======================================

    // Note that none of these expressions are allowed to consume values because if they did,
    //  they would lead to asset loss: the values they consume aren't stored anywhere.
    rule <k> (E1 = E2) : ! bool
             =>
             E1 : ?Tau ~> assertEnv(Gamma) ~>
             E2 : ?Tau ~> assertEnv(Gamma)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    rule (S in X) : ! bool
         =>
         X provides {?_} ?Tau ~>
         S selects {?_} demote(?Tau)

    rule <k> (A and B) : ! bool
             =>
             A : ! bool ~> assertEnv(Gamma) ~>
             B : ! bool ~> assertEnv(Gamma)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    rule <k> (A or B) : ! bool
             =>
             A : ! bool ~> assertEnv(Gamma) ~>
             B : ! bool ~> assertEnv(Gamma)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    rule <k> (not A) : ! bool
             =>
             A : ! bool ~> assertEnv(Gamma)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

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

    // NOTE: comm attribute doesn't seem to work for some reason...
    syntax TypeQuant ::= TypeQuant "+" TypeQuant [function, functional, comm, assoc]
                       | TypeQuant "-" TypeQuant [function, functional]

    rule Q + empty => Q
    rule empty + R => R
    rule _ + every => every
    rule every + _ => every
    rule nonempty + R => nonempty requires empty <Q R andBool R <Q every
    rule Q + nonempty => nonempty requires empty <Q Q andBool Q <Q every
    rule ! + R => nonempty requires empty <Q R andBool R <Q every
    rule Q + ! => nonempty requires empty <Q Q andBool Q <Q every
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
    rule ((X |-> T) As) <=Env B => (T <=Ty typeof(B, X)) andBool As <=Env B

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
    /* rule 0 : empty nat => . */
    /* rule 1 : ! nat => . */
    /* rule I:Int : nonempty nat => . */
    /*     requires I >Int 1 */
    rule I:Int : any nat => .
        requires I >=Int 0

    rule I:Int : T => typeError(I : T)
        requires (_:TypeQuant nat) :/=K T orBool I <Int 0

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
    // Transformer Types
    // =======================================
    rule <k> (\ X : T . E) : ! (T ~~> S)
             =>
             insert(X, T) ~> E : S ~> drop(X) ~>
             assertEnv(Gamma)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

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

    rule <k> new C.T provides {every} ! C.T => . ... </k>
        <typeEnv> ... this |-> (! C) ... </typeEnv>
        <types> ... C |-> types((T |-> _) _) ... </types>

    // =======================================
    // Selector typing
    // =======================================
    rule everything selects {every} _ => .

    rule <k> E:Expr selects {Q} T
             =>
             E : Q ?T2 ~> assertEnv(Gamma) ~> typeEq(elemtype(?T2), T)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    rule <k> (Q X : T such that E) selects {Q} T
             =>
             insert(X, T) ~> E : ! bool ~> drop(X) ~>
             assertEnv(Gamma)
             ...
         </k>
         <typeEnv> Gamma </typeEnv>

    // =======================================
    // Flow typing
    // =======================================
    syntax Stmt ::= validSelect(Selector, TypeQuant, TypeQuant)

    rule validSelect(Sel, R, Q)
         =>
         checkThat(min(Q, R) <Q every) ~>
         checkThat((Q =/=K every) orBool (_:Expr :=K Sel))

    // TODO: Implement transformer checking
    rule S --[ Sel ]-> D =>
        // TODO: These mutable checks are wrong. We don't care if the types inside the storages are mutable, but if the storages themselves are mutable.
        // TODO: We can put the checks inside the storage rules (i.e., provides and accepts) themselves.
        S provides {?Q} ?Tau ~> mutable(?Tau) ~>
        Sel selects {?R} demote(?Tau) ~>
        validSelect(Sel, ?R, ?Q) ~>
        update(S, typeof(S) -Ty ?R)
        D accepts ?Tau ~> mutable(?Tau) ~>
        update(D, typeof(D) +Ty min(?Q, ?R))

    // =======================================
    // If Statement, Expr
    // =======================================
    rule <k> if E { S1:Stmt } else { S2:Stmt }
             =>
             E : ! bool ~> assertEnv(Gamma) ~>
             S1 ~> assertEnv(?Delta) ~>
             setEnv(Gamma) ~>
             S2 ~> assertEnv(?Xi) ~>
             setEnv(join(?Delta, ?Xi))
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    rule <k> (if E { E1 } else { E2 }) : Tau
             =>
             E : ! bool ~> assertEnv(Gamma) ~>
             E1 : Tau ~> assertEnv(?Delta) ~>
             setEnv(Gamma) ~>
             E2 : Tau ~> assertEnv(?Xi) ~>
             setEnv(join(?Delta, ?Xi))
             ...
         </k>
        <typeEnv> Gamma </typeEnv>

    // =======================================
    // Try-Catch
    // =======================================
    rule <k> try { S1 } catch (X : T) { S2 }
             =>
             S1 ~> assertEnv(?Delta) ~>
             setEnv(Gamma) ~>
             insert(X, T) ~> S2 ~> drop(X) ~> assertEnv(?Xi) ~>
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
             checkThat(notBool(isAsset(?Tau))) ~>
             assertEnv(Gamma)
             ...
         </k>
        <typeEnv> Gamma </typeEnv>


    // =======================================
    // Expression statement
    // =======================================
    rule expr(E) => E : ?Sigma ~> checkThat(notBool(isAsset(?Sigma)))

    // =======================================
    // View calls
    // =======================================
    rule <k> X.F(Args) : T => packed ~> checkEach(Args, FormalArgs) ... </k>
         <typeEnv> ... X |-> (! C) ... </typeEnv>
         <functions> ... C |-> functions((F |-> view(T, FormalArgs, _)) _) ... </functions>

    // =======================================
    // Internal calls
    // =======================================
    rule <k> this.F(Args) : T => packed ~> checkEach(Args, FormalArgs) ~> assertPartialEnv(this |-> C) ... </k>
        <typeEnv> ... this |-> (! C) ... </typeEnv>
        <functions> ... C |-> functions((F |-> transaction(_ : T, FormalArgs, _)) _) ... </functions>

    // =======================================
    // External calls
    // =======================================
    rule <k> X.F(Args) : T => packed ~> checkEach(Args, FormalArgs) ~> assertEnv(Gamma) ... </k>
        <typeEnv> ((X |-> (! D)) _) #as Gamma </typeEnv>
        <functions> ... D |-> functions((F |-> transaction(_ : T, FormalArgs, _)) _) ... </functions>

    // =======================================
    // Unpack
    // =======================================
    rule <k> unpack(F) => . ... </k>
        <typeEnv> Gamma (this |-> (! C)) (.Map => this.F |-> T) </typeEnv>
        <fields> ... C |-> fields((F |-> T) _) ... </fields>
        requires notBool(this.F in keys(Gamma))

    // =======================================
    // Pack
    // =======================================
    rule <k> pack => . ... </k>
        <typeEnv> ((this |-> (! C)) _) #as Gamma => removeAll(Gamma, keys(fieldsOf(C))) </typeEnv>
        requires restrict(Gamma, keys(fieldsOf(C))) <=Env fieldsOf(C)

    rule <k> pack => . ... </k>
        <typeEnv> Gamma </typeEnv>
        requires notBool(this in keys(Gamma))

    syntax Stmt ::= "packed"
    rule <k> packed => . ... </k>
        <typeEnv> (this |-> (! C)) Gamma </typeEnv>
        requires intersectSet(keys(fieldsOf(C)), keys(Gamma)) ==K .Set

    rule <k> packed => . ... </k>
        <typeEnv> Gamma </typeEnv>
        requires notBool(this in keys(Gamma))

    rule exit => .

    // =======================================
    // Type modifier checking
    // =======================================
    syntax Bool ::= isAsset(Type) [function, functional]
                  | isAsset(BaseType) [function, functional]
                  | anyAsset(VarDefs) [function, functional]

    rule isAsset(Q:TypeQuant T) => Q =/=K empty andBool isAsset(T)
    rule isAsset(T:Var) => asset in modifiers(T)
    rule isAsset(_:Collection T) => isAsset(T)
    rule isAsset({ Fields }) => anyAsset(Fields)
    rule isAsset(_:BaseType) => false [owise]

    rule anyAsset(.VarDefs) => false
    rule anyAsset((_ : T), Defs) => isAsset(T) orBool anyAsset(Defs)

    syntax Stmt ::= allNonAsset(Map)

    rule allNonAsset(.Map) => .
    rule allNonAsset((_ |-> T:Type) Rest) => allNonAsset(Rest)
        requires notBool(isAsset(T))

    syntax Bool ::= isConsumable(Type) [function, functional]
    rule isConsumable(Q:TypeQuant T) => (consumable in modifiers(T)) orBool notBool(isAsset(Q T))

    syntax Stmt ::= mutable(Type)
    rule <k> mutable(_:TypeQuant T) => . ... </k>
        requires notBool(immutable in modifiers(T))

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

    syntax Map ::= makeEnv(Set) [function, functional]
    rule makeEnv(.Set) => .Map
    rule makeEnv(SetItem((X : T):VarDef) Rest) => (X |-> T) makeEnv(Rest)

    syntax Map ::= makeFieldEnv(Map) [function, functional]
    rule makeFieldEnv(.Map) => .Map
    rule makeFieldEnv((X |-> T) Rest) => (this.X |-> T) makeFieldEnv(Rest)

    syntax Map ::= fieldsOf(Var) [function, functional]
    rule [[ fieldsOf(C) => makeFieldEnv(Fields) ]]
        <fields> ... C |-> fields(Fields) ... </fields>

    syntax Set ::= varDefsToSet(VarDefs) [function, functional]
    rule varDefsToSet(.VarDefs) => .Set
    rule varDefsToSet(Def, Defs) => SetItem(Def) varDefsToSet(Defs)
endmodule

