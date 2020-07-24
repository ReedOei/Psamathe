require "flow-common.k"

module FLOW
    imports DOMAINS
    imports COLLECTIONS

    imports FLOW-SYNTAX
    imports FLOW-COMMON

    // TODO: Split this out?
    // TODO: Or replace by the improved "identified by" system?
    syntax Link ::= Val "<=>" Val
    syntax Linking ::= linking(BaseType, Set)

    rule linking(T, SetItem(K <=> V1) SetItem(K <=> V2) Rest) => linking(T, SetItem(K <=> combine(V1, V2)) Rest)

    syntax Val ::= Linking "[" Val "]" [function, functional]
    rule linking(_, (SetItem(K <=> V) _))[K] => V

    syntax Val ::= ownerOf(Linking, Val) [function, functional]
    rule ownerOf(linking(_, SetItem(K <=> Vs) _), V) => K
        requires V contained_in Vs

    syntax Bool ::= hasOwner(Linking, Val) [function, functional]
    rule hasOwner(linking(_, .Set), _) => false
    rule hasOwner(linking(T, SetItem(_ <=> Vs) L), V) => (V contained_in Vs) orBool hasOwner(linking(T, L), V)

    syntax Val ::= values(Linking) [function, functional]
    rule values(linking(T, .Set)) => emptyValue(T)
    rule values(linking(T, SetItem(_ <=> C) L)) => combine(C, values(linking(T, L)))

    syntax StorageLoc ::= loc(Int)
    syntax StorageVal ::= StorageLoc
    syntax BasicVal ::= Int
                      | Bool
                      | String
                      | EmptyVal
                      | "none"
                      | some(BasicVal)
                      | Set
                      | List
                      | Map
                      | Linking
    syntax Resource ::= resource(BaseType, BasicVal)
    syntax FlowError ::= flowError(String)
    syntax Val ::= Resource | FlowError
    syntax KResult ::= Val | Vals | StorageVal | SelectorVal

    syntax Var ::= "Base"

    configuration
        <common />
        <lookup> this |-> loc(-1) </lookup>
        <storage> loc(-1) |-> resource(Base, .Map) </storage>
        <catchStack> .List </catchStack>

    rule execute => .

    // =================================
    // Sequence
    // =================================
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // =================================
    // Pass
    // =================================
    rule pass => . [structural]

    // =================================
    // Variable declaration
    // =================================
    context var _ : _ := HOLE in _:Stmt
    rule <k> var X : T := V:Val in S:Stmt => insert(X, loc(I)) ~> S ~> drop(X) ... </k>
        <storage> ... .Map => loc(I) |-> coerce(V, T) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    // =================================
    // Environment Helpers
    // =================================
    syntax Stmt ::= insert(Var, StorageLoc)
                  | resetEnv(Map)
                  | "dropCatch"

    rule <k> insert(X, Loc) => . ... </k>
        <lookup> ... .Map => X |-> Loc ... </lookup>
    rule <k> resetEnv(Lookup) => . ... </k>
        <lookup> _ => Lookup </lookup>
    rule <k> dropCatch => . ... </k>
        <catchStack> ListItem(_) => .List ... </catchStack>

    syntax Val ::= coerce(Val, Type) [function, functional]
    rule coerce(resource(R, V), _ R) => resource(R, V)
    rule coerce(resource(_, emptyval), empty X:Var) => resource(X, emptyval)
    rule coerce(resource(_, emptyval), empty option R) => resource(option R, none)
    rule coerce(resource(_, emptyval), empty set R) => resource(set R, .Set)
    rule coerce(resource(_, emptyval), empty list R) => resource(list R, .List)
    rule coerce(resource(_, emptyval), any option R) => resource(option R, none)
    rule coerce(resource(_, emptyval), any set R) => resource(set R, .Set)
    rule coerce(resource(_, emptyval), any list R) => resource(list R, .List)

    syntax Stmt ::= drop(Var)
                  | dropLoc(StorageLoc)
    rule <k> drop(X) => . ... </k>
        <lookup> ... X |-> _ => .Map ... </lookup>

    rule <k> dropLoc(Loc) => . ... </k>
        <storage> ... Loc |-> _ => .Map ... </storage>

    // =================================
    // Check-In
    // =================================
    rule Sel in R => checkIn(Sel, resolveStorage(R))

    syntax Expr ::= checkIn(Selector, Storage) [strict]

    rule <k> checkIn(Sel, Loc) => resource(bool, select(Sel, SV) contained_in SV) ... </k>
        <storage> ... Loc |-> SV ... </storage>

    // =================================
    // Literals
    // =================================
    rule I:Int => resource(nat, I)
        requires I >=Int 0
    rule B:Bool => resource(bool, B)
    rule S:String => resource(string, S)
    rule emptyval => resource(?_, emptyval)

    // =================================
    // Simple arithmetic and boolean expressions
    // =================================
    // TODO: I would like to remove all this resource stuff at some point
    //       The typechecker can also compile this stuff into the correct instructions to permit erasing all these runtime types.
    context HOLE + _
    context _ + HOLE
    rule resource(nat, I1) + resource(nat, I2) => resource(nat, I1 +Int I2)
    rule resource(nat, I1) - resource(nat, I2) => resource(nat, I1 -Int I2)

    context _ = HOLE
    context HOLE = _
    rule resource(R, A) = resource(R, B) => A ==K B

    context HOLE < _
    context _ < HOLE
    rule resource(nat, I1) < resource(nat, I2) => resource(bool, I1 <Int I2)

    context HOLE <= _
    context _ <= HOLE
    rule resource(nat, I1) <= resource(nat, I2) => resource(bool, I1 <=Int I2)

    context HOLE and _
    rule resource(bool, true) and B => B
    rule resource(bool, false) and _ => resource(bool, false)

    context HOLE or _
    rule resource(bool, true) or _ => resource(bool, true)
    rule resource(bool, false) or B => B

    context not HOLE
    rule not resource(bool, B) => resource(bool, notBool B)

    context (if HOLE { _ } else { _ }):IfExpr
    rule (if resource(bool, true) { A } else { _ }):IfExpr => A
    rule (if resource(bool, false) { _ } else { B }):IfExpr => B

    context if HOLE { _:Stmt } else { _:Stmt }
    rule if resource(bool, true) { A:Stmt } else { _ }  => A
    rule if resource(bool, false) { _ } else { B:Stmt } => B

    // =================================
    // Variable lookup
    // =================================
    rule <k> X => demoteVal(Val) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... Loc |-> Val ... </storage>

    rule <k> X . F => demoteVal(Val) ... </k>
        <lookup> ... X |-> XLoc ... </lookup>
        <storage> ... (XLoc |-> resource(_, (F |-> Loc) _)) (Loc |-> Val) ... </storage>

    syntax Expr ::= resolveStorage(Storage)

    context resolveStorage(evaluate(HOLE))

    rule resolveStorage(evaluate(V:Val)) => resolveStorage(V)
    rule resolveStorage(I:Int) => resolveStorage(resource(nat, I))
        requires I >=Int 0
    rule resolveStorage(S:String) => resolveStorage(resource(string, S))
    rule resolveStorage(B:Bool) => resolveStorage(resource(bool, B))
    rule <k> resolveStorage(resource(R, V)) => loc(I) ... </k>
        <storage> ... .Map => loc(I) |-> resource(R, V) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    rule resolveStorage(consume) => consume
    rule <k> resolveStorage(X) => Loc ... </k>
        <lookup> ... X |-> Loc ... </lookup>
    rule <k> resolveStorage(X . F) => Loc ... </k>
        <lookup> ... X |-> XLoc ... </lookup>
        <storage> ... XLoc |-> resource(_, (F |-> Loc) _) ... </storage>
    rule resolveStorage(loc(I)) => loc(I)

    // NOTE: All types are always stored as their demoted value, so we simply need to demote the type.
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(R, V)) => resource(demote(R), V)

    // =================================
    // Try-Catch:
    // =================================
    // Stores the variable/type to catch, the handler, the lookup table, the storage to restore to, and the continuation.
    syntax Stmt ::= catch(Var, Type, Stmt, Map, Map, K)

    context revert(HOLE)

    rule <k> try { S1 } catch (X : T) { S2 } ~> K => S1 ~> dropCatch </k>
        <lookup> Lookup </lookup>
        <storage> Storage </storage>
        <catchStack> .List => ListItem(catch(X, T, S2, Lookup, Storage, K)) ... </catchStack>

    rule <k> revert(V:Val) ~> _ => var X : T := V in S ~> K </k>
        <lookup> _ => Lookup </lookup>
        <storage> _ => Storage </storage>
        <catchStack> ListItem(catch(X, T, S, Lookup, Storage, K)) => .List ... </catchStack>

    // =================================
    // Flows:
    // =================================
    context _ --[ HOLE ]-> _
    rule S --[ Sel:SelectorVal ]-> D => handleFlow(Sel, resolveStorage(S), resolveStorage(D))

    syntax Stmt ::= handleFlow(SelectorVal, Storage, Storage) [seqstrict]

    // Consume
    rule <k> handleFlow(Sel, SourceLoc, consume) => . ... </k>
        <storage> ... (SourceLoc |-> (SV => subtract(SV, select(Sel, SV)))) ... </storage>
        requires select(Sel, SV) contained_in SV

    // Type sources
    // NOTE: The only valid selectors for a source must evaluate to a resource value.
    rule <k> handleFlow(resource(R, V), new C.T, DestLoc) => put(combine(convert(resource(R, V), DestR), resource(DestR, Cur)), DestLoc) ... </k>
        <lookup> ... this |-> Loc ... </lookup>
        <storage>
            ...
            (Loc |-> resource(C, Storage))
            (DestLoc |-> resource(DestR, Cur))
            =>
            (Loc |-> resource(C, Storage))
            ...
        </storage>
        requires notBool(unique in modifiers(C.T))

    // TODO: This is a bit ugly, should simplify.
    rule <k> handleFlow(resource(R, V), new C.T, DestLoc) => put(combine(convert(resource(R, V), DestR), resource(DestR, Cur)), DestLoc) ... </k>
        <lookup> ... this |-> Loc ... </lookup>
        <storage>
            ...
            (Loc |-> resource(C, (T |-> SourceLoc) Storage))
            (SourceLoc |-> resource(SourceR, CurVals))
            (DestLoc |-> resource(DestR, Cur))
            =>
            (Loc |-> resource(C, (T |-> SourceLoc) Storage))
            (SourceLoc |-> combine(convert(resource(R, V), SourceR), resource(SourceR, CurVals)))
            ...
        </storage>
        requires (unique in modifiers(C.T))
         andBool (notBool(convert(resource(R, V), SourceR) contained_in resource(SourceR, CurVals)))

    rule <k> handleFlow(Sel, SourceLoc, DestLoc) => put(combine(convert(select(Sel, SV), DestR), resource(DestR, Cur)), DestLoc) ... </k>
        <storage>
            ...
            (SourceLoc |-> SV)
            (DestLoc |-> resource(DestR, Cur))
            =>
            (SourceLoc |-> subtract(SV, select(Sel, SV)))
            ...
        </storage>
        requires select(Sel, SV) contained_in SV

    syntax Stmt ::= put(Val, StorageLoc)

    rule put(flowError(Err), _) => revert(flowError(Err))
    rule <k> put(R:Resource, Loc) => . ... </k>
        <storage> ... .Map => Loc |-> R ... </storage>

    syntax Resource ::= select(SelectorVal, Resource) [function, functional]

    // ==================================
    // Select
    // TODO: Handle selectors that need to be converted (or maybe just convert by default), such as selecting from a set with a list.
    // ==================================
    rule select(everything, R) => R
    rule select(resource(R, V), resource(R, _)) => resource(R, V)
    rule select(resource(R, V), resource(option Q R, _)) => resource(option Q R, some(V))
    rule select(resource(R, V), resource(set Q R, _)) => resource(set Q R, SetItem(V))
    rule select(resource(R, V), resource(list Q R, _)) => resource(list Q R, ListItem(V))

    // ==================================
    // Subtract
    // ==================================
    syntax Resource ::= subtract(Resource, Resource) [function, functional]
    rule subtract(resource(nat, A), resource(nat, B)) => resource(nat, A -Int B)
    rule subtract(resource(X:Var, A), resource(X, A)) => resource(X, emptyval)
        requires X =/=K nat
    rule subtract(resource(X.T, A), resource(X.T, A)) => resource(X.T, emptyval)
    rule subtract(resource(X.T, A), resource(X.T, A)) => resource(X.T, emptyval)

    rule subtract(resource(option R, A), resource(option R, none)) => resource(option R, A)
    rule subtract(resource(option R, some(A)), resource(option R, some(A))) => resource(option R, none)

    rule subtract(resource(set R, A), resource(set R, B)) => resource(set R, A -Set B)

    rule subtract(resource(list R, A), resource(list R, .List)) => resource(list R, A)
    rule subtract(resource(list R, A), resource(list R, ListItem(B) Rest))
         => subtract(resource(list R, remove(A, B)), resource(list R, Rest))

    rule subtract(resource(R, A), resource(S, _)) => resource(R, A)
        requires R =/=K S

    // ==================================
    // contained_in
    // ==================================
    syntax Bool ::= Val "contained_in" Val [function, functional]

    rule resource(nat, A) contained_in resource(nat, B) => A <=Int B
    rule resource(X:Var, A) contained_in resource(X, B) => A ==K B
        requires X =/=K nat
    rule resource(X.T, A) contained_in resource(X.T, B) => A ==K B

    rule resource(option R, none) contained_in resource(option R, _) => true
    rule resource(option R, some(_)) contained_in resource(option R, none) => false
    rule resource(option Q R, some(A)) contained_in resource(option Q R, some(B))
         => resource(R, A) contained_in resource(R, B)

    rule resource(set R, A) contained_in resource(set R, B) => A is_subset_of B

    // TODO: These are not efficiently written, but they are correctly written (I hope...)
    rule resource(list R, .List) contained_in resource(list R, _) => true
    rule resource(list R, ListItem(_) _) contained_in resource(list R, .List) => false
    rule resource(list R, ListItem(A) Rest) contained_in resource(list R, B)
         =>
         (A in B) andBool (resource(list R, Rest) contained_in resource(list R, remove(B, A)))

    rule resource(_, _) contained_in resource(_ ~~> _, _) => false
    rule resource(_ ~~> _, _) contained_in resource(_, _) => false

    // ==================================
    // single : e -> c, where c is fungible and e is it's element type.
    // ==================================
    syntax Val ::= single(BaseType, BasicVal) [function, functional]
    rule single(X:Var, V) => resource(X, V)
    rule single(option R, V) => resource(option R, some(V))
    rule single(set R, V) => resource(set R, SetItem(V))
    rule single(list R, V) => resource(list R, ListItem(V))

    // ==================================
    // Convert resources: Takes a resource value and converts it to be compatible with the specified type
    //  - e.g., an option => set conversion makes `none` into the empty set and `some(A)` into a singleton containing A
    // ==================================
    syntax Val ::= convert(Resource, BaseType) [function, functional]

    rule convert(resource(_, emptyval), Target) => emptyValue(Target)
    rule convert(resource(_:Var, A), Target) => single(Target, A)

    rule convert(resource(set _, .Set), Target) => emptyValue(Target)
    rule convert(resource(set R, SetItem(A) Rest), Target) => combine(single(Target, A), convert(resource(set R, Rest), Target))

    rule convert(resource(list _, .List), Target) => emptyValue(Target)
    // Note we do pure at the end---this is to maintain the order of lists (when it makes sense to do so)
    rule convert(resource(list R, ListItem(A) Rest), Target) => combine(convert(resource(list R, Rest), Target), single(Target, A))

    rule convert(resource(option _, none), Target) => emptyValue(Target)
    rule convert(resource(option _, some(A)), Target) => single(Target, A)

    // ==================================
    // Combine resources: takes two collections of values and makes a single collection.
    // ==================================
    syntax Val ::= combine(Val, Val) [function, functional]

    // Error propagation
    rule combine(flowError(E), _) => flowError(E)
    rule combine(_, flowError(E)) => flowError(E)

    rule combine(resource(R, A), resource(R, emptyval)) => resource(R, A)
    rule combine(resource(nat, A), resource(nat, B)) => resource(nat, A +Int B)
    rule combine(resource(X:Var, _), resource(_, B)) => flowError("Destination already full!")
        requires X =/=K nat andBool B =/=K emptyval
    rule combine(resource(X.T, _), resource(X.T, B)) => flowError("Destination already full!")
        requires B =/=K emptyval

    rule combine(resource(option R, A), resource(option R, none)) => resource(option R, A)
    rule combine(resource(option R, none), resource(option R, some(B))) => resource(option R, some(B))
    rule combine(resource(option R, some(_)), resource(option R, some(_))) => flowError("Destination already full!")

    rule combine(resource(set R, SetItem(A) _), resource(set R, SetItem(A) _)) => flowError("Tried to combine two non-disjoint sets!")
    rule combine(resource(set R, A:Set), resource(set R, B:Set)) => resource(set R, A |Set B) [owise]

    // Combine as `B A` instead of `A B`, because the new values should be **appended**, not prepended.
    rule combine(resource(list R, A:List), resource(list R, B:List)) => resource(list R, B A)

    // ==================================
    // ==================================
    syntax Resource ::= emptyValue(BaseType) [function, functional]
    rule emptyValue(nat) => resource(nat, 0)
    rule emptyValue(X:Var) => resource(X, emptyval)
        requires X =/=K nat
    rule emptyValue(option R) => resource(option R, none)
    rule emptyValue(set R) => resource(set R, .Set)
    rule emptyValue(list R) => resource(list R, .List)

    // =================================
    // Expression Statements
    // =================================
    context expr(HOLE)
    rule expr(_:Val) => .

    syntax Expr ::= evaluate(Expr) [strict]
    rule evaluate(V:Val) => V

    // =================================
    // Linear Lookup Value Helper
    // =================================
    syntax Expr ::= lookupVal(StorageLoc)
    rule <k> lookupVal(Loc) => V ... </k>
        <storage> ... Loc |-> V => .Map ... </storage>

    // =================================
    // Function calls:
    // =================================
    syntax Stmt ::= setupArgs(Exprs, VarDefs, Stmt)
                  | cleanEnv(Set)
                  | invoke(StorageLoc, Exprs, VarDefs, Stmt)

    rule setupArgs(.Exprs, .VarDefs, S) => S
    rule setupArgs((E, Es):Exprs, (Y : T, Defs2), S) => var Y : T := E in setupArgs(Es, Defs2, S)

    rule <k> cleanEnv(ToRemove) => . ... </k>
        <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup>

    rule <k> invoke(Loc, Args, FormalArgs, Body) => setupArgs(Args, FormalArgs, cleanEnv(keys(Lookup)) insert(this, Loc) Body) ~> resetEnv(Lookup) ... </k>
        <lookup> Lookup </lookup>

    // Transactions
    rule <k> X.T(ActualArgs) => invoke(Loc, ActualArgs, FormalArgs, insert(RetVar, loc(I)) S) ~> lookupVal(loc(I)) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... (Loc |-> resource(C, _)) (.Map => loc(I) |-> emptyValue(RetType)) ... </storage>
        <functions> ... C |-> (SetItem(transaction(T, RetVar : _:TypeQuant RetType, FormalArgs, S)) _) ... </functions>
        <freshCounter> I => I +Int 1 </freshCounter>

    // Views
    rule <k> X.F(ActualArgs) => invoke(Loc, ActualArgs, FormalArgs, handleFlow(everything, resolveStorage(evaluate(E)), loc(I))) ~> lookupVal(loc(I)) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... (Loc |-> resource(C, _)) (.Map => loc(I) |-> emptyValue(RetType)) ... </storage>
        <functions> ... C |-> (SetItem(view(F, _:TypeQuant RetType, FormalArgs, E)) _) ... </functions>
        <freshCounter> I => I +Int 1 </freshCounter>

    // TODO: Mabye replace this by a more efficient system (e.g., a call stack cell)
    rule exit ~> S:Stmt => exit
        requires resetEnv(_) :/=K S
        [structural]
    rule exit ~> resetEnv(Lookup) => resetEnv(Lookup)
        [structural]

    // ============================
    // New contract
    // ============================
    rule <k> new C(Args)
             =>
             initSources(loc(I), Types) ~> initFields(loc(I), Fields) ~> invoke(loc(I), Args, FormalArgs, S) ~> lookupVal(loc(I))
             ...
         </k>
        <storage> ... .Map => loc(I) |-> resource(C, .Map) ... </storage>
        <fields> ... C |-> Fields ... </fields>
        <constructors> ... C |-> constructor(FormalArgs, S) ... </constructors>
        <types> ... C |-> Types ... </types>
        <freshCounter> I => I +Int 1 </freshCounter>

    syntax Stmt ::= initSources(StorageLoc, Set)

    rule initSources(_, .Set) => .

    // Don't bother creating a source for the contract type itself
    rule <k> initSources(Loc, SetItem(type(C, _, _)) Rest) => initSources(Loc, Rest) ... </k>
        <storage> ... Loc |-> resource(C, _) ... </storage>

    rule <k> initSources(Loc, SetItem(type(Name, _, _)) Rest) => initSources(Loc, Rest) ... </k>
        <storage>
            ...
            (Loc |-> resource(C, Fs))
            =>
            (Loc |-> resource(C, (Name |-> loc(I)) Fs))
            (loc(I) |-> resource(set ! Name, .Set))
            ...
        </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
        requires Name =/=K C

    syntax Stmt ::= initFields(StorageLoc, Set)

    rule initFields(_, .Set) => .
    rule <k> initFields(Loc, SetItem(X : _:TypeQuant T) Rest) => initFields(Loc, Rest) ... </k>
        <storage>
            ...
            (Loc |-> resource(C, Fs))
            =>
            (Loc |-> resource(C, (X |-> loc(I)) Fs))
            (loc(I) |-> emptyValue(T))
            ...
        </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    // ==================================
    // Pack
    // ==================================
    syntax Stmt ::= doPack(Map)

    rule <k> pack => doPack(Fs) ... </k>
        <lookup> ... this |-> Loc ... </lookup>
        <storage> ... Loc |-> resource(_, Fs) ... </storage>

    rule doPack(.Map) => .
    rule <k> doPack((X |-> _) Rest) => doPack(Rest) ... </k>
        <lookup> Lookup => removeAll(Lookup, SetItem(this.X)) </lookup>

    // ==================================
    // Unpack
    // ==================================
    rule <k> unpack(X) => . ... </k>
        <lookup>
            ...
            (this |-> Loc)
            =>
            (this |-> Loc)
            (this.X |-> XLoc)
            ...
        </lookup>
        <storage> ... Loc |-> resource(_, (X |-> XLoc) _) ... </storage>

    rule <k> unpack(X) => . ... </k>
        <lookup> ... X |-> _ ... </lookup>
endmodule

