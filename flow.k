require "substitution.k"
require "flow-common.k"

module FLOW
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS
    imports SUBSTITUTION

    syntax StorageLoc ::= loc(Int) [freshGenerator, function, functional]
    syntax SpecialStorage ::= StorageLoc
    syntax BasicVal ::= Val
                      | Set
                      | List
                      | Map
                      | some(Val)
                      | "none" [token]
                      // This can be stored in the middle of a transaction, but not at the end, unless the reference is temporary.
                      | "emptySingleton" [token]
                      | StorageLoc
    syntax ErrorVal ::= revert(String)
    syntax Resource ::= resource(BaseType, BasicVal)
    syntax Storage ::= Resource
    syntax ResourceVal ::= Resource
                         | ErrorVal
    syntax KResult ::= ResourceVal
                     | SpecialSelect

    syntax Id ::= "NoContract" [token]
                // A special Id to be used as the "location" of the current contract in the global scope.
                | "#null" [token]
    syntax KVar ::= Id

    configuration
        <common />
        <storage> .Map </storage>
        <lookup> .Map </lookup>
        <localTypeEnv> .Map </localTypeEnv>
        <currentContract> NoContract </currentContract>
        <transformerStack> .List </transformerStack>

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // Pass
    rule pass => .

    // Temporary variable declaration
    rule <k> var X : T => . ... </k>
        <localTypeEnv> ... .Map => X |-> T </localTypeEnv>
        <lookup> ... .Map => X |-> !Loc:StorageLoc </lookup>
        <storage> ... .Map => !Loc |-> defaultValue(T) ... </storage>

    rule I:Int => resource(nat, I)
        requires I >=Int 0
    rule B:Bool => resource(bool, B)
    rule S:String => resource(string, S)

    // Simple arithmetic and boolean expressions
    // TODO: I would like to remove all this resource stuff at some point
    //       The typechecker can also compile this stuff into the correct instructions to permit erasing all these runtime types.
    rule resource(nat, I1) + resource(nat, I2) => resource(nat, I1 +Int I2)
    rule resource(nat, I1) - resource(nat, I2) => resource(nat, I1 -Int I2)

    rule resource(R, A) = resource(R, B) => A ==K B

    rule resource(nat, I1) < resource(nat, I2) => resource(bool, I1 <Int I2)
    rule resource(nat, I1) <= resource(nat, I2) => resource(bool, I1 <=Int I2)

    rule resource(bool, true) and B => B
    rule resource(bool, false) and _ => resource(bool, false)
    rule resource(bool, true) or _ => resource(bool, true)
    rule resource(bool, false) or B => B
    rule not resource(bool, B) => resource(bool, notBool B)

    rule if resource(bool, true) then A else _ => A
    rule if resource(bool, false) then _ else B => B

    // Variable lookup
    rule <k> X => demote(Val) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... Loc |-> Val ... </storage>

    rule <k> X . F => demote(Val) ... </k>
        <lookup> ... X |-> XLoc ... </lookup>
        <storage> ... (XLoc |-> resource(_, (F |-> Loc) _)) (Loc |-> Val) ... </storage>

    syntax K ::= resolveStorage(Storage)
               | resolved(SpecialStorage)

    // NOTE: Some unfortunate duplication here...
    rule resolveStorage(I:Int) => resolveStorage(resource(nat, I))
        requires I >=Int 0
    rule resolveStorage(S:String) => resolveStorage(resource(string, S))
    rule resolveStorage(B:Bool) => resolveStorage(resource(bool, B))
    rule resolveStorage(consume) => resolved(consume)
    rule resolveStorage(new C(Args)) => resolved(new C(Args))
    rule resolveStorage(Loc:StorageLoc) => resolved(Loc)
    rule <k> resolveStorage(X) => resolved(Loc) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
    rule <k> resolveStorage(X . F) => resolved(Loc) ... </k>
        <lookup> ... X |-> XLoc ... </lookup>
        <storage> ... XLoc |-> resource(R, (F |-> Loc) _) ... </storage>
    rule <k> resolveStorage(resource(R, V)) => resolved(!Loc) ... </k>
        <storage> ... .Map => !Loc:StorageLoc |-> resource(R, V) ... </storage>

    // TODO: Finish this
    syntax Resource ::= demote(Resource) [function, functional]

    rule demote(resource(nat, V)) => resource(nat, V)
    rule demote(resource(bool, V)) => resource(bool, V)
    rule demote(resource(string, V)) => resource(string, V)
    rule demote(resource(address, V)) => resource(address, V)
    rule demote(resource(unit, V)) => resource(unit, V)

    // =================================
    // Flows:
    // =================================
    rule S --[ Sel ]-> D => resolveStorage(S) ~> resolveStorage(D) ~> selector(Sel)

    // NOTE: For some reason, K doesn't like the strict declaration in the
    //  original flow construct, but here's another one that it does work for...
    syntax K ::= selector(Selector) [strict(1)]
               | selectorSource(Selector, SpecialStorage) [strict(1)]
               | handleFlow(Selector, SpecialStorage, SpecialStorage) [strict(1)]

    rule resolved(Source) ~> K ~> selector(Sel) => K ~> selectorSource(Sel, Source)
    rule resolved(Dest) ~> selectorSource(Sel, Source) => handleFlow(Sel, Source, Dest)

    rule <k> handleFlow(Sel, SourceLoc, consume) => . ... </k>
        <storage> ... (SourceLoc |-> (SV => subtract(SV, select(Sel, SV)))) ... </storage>
        requires select(Sel, SV) contained_in SV

    rule <k> handleFlow(Sel, new C(Args), D)
             =>
             initFields(!Loc:StorageLoc, Fields) ~> setupArgs(Args, FormalArgs) ~> cleanEnv(keys(Env)) ~> unpack(!Loc) ~> S ~> pack(Old, Lookup, Env) ~> handleFlow(Sel, !Loc, D)
             ...
         </k>
        <storage> ... .Map => !Loc |-> resource(C, .Map) ... </storage>
        <localTypeEnv> Env </localTypeEnv>
        <lookup> Lookup </lookup>
        <currentContract> Old => C </currentContract>
        <fields> ... C |-> Fields ... </fields>
        <constructors> ... C |-> constructor(FormalArgs, S) ... </constructors>

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

    syntax Resource ::= select(Selector, Resource) [function, functional]

    // Selection (includes select, subtract, and contains)
    // TODO: Handle selectors that need to be converted (or maybe just convert by default), such as selecting from a set with a list.
    rule select(everything, R) => R
    rule select(resource(R, V), resource(R, _)) => resource(R, V)
    rule select(resource(R, V), resource(option Q R, _)) => resource(option Q R, some(V))
    rule select(resource(R, V), resource(set Q R, _)) => resource(set Q R, SetItem(V))
    rule select(resource(R, V), resource(list Q R, _)) => resource(list Q R, ListItem(V))

    syntax Resource ::= subtract(Resource, Resource) [function, functional]

    rule subtract(resource(nat, A), resource(nat, B)) => resource(nat, A -Int B)
    rule subtract(resource(X:Id, A), resource(X, A)) => resource(X, emptySingleton)
        requires X =/=K nat
    rule subtract(resource(X.T, A), resource(X.T, A)) => resource(X.T, emptySingleton)

    rule subtract(resource(option R, A), resource(option R, none)) => resource(option R, A)
    rule subtract(resource(option R, some(A)), resource(option R, some(A))) => resource(option R, none)

    rule subtract(resource(set R, A), resource(set R, B)) => resource(set R, A -Set B)

    rule subtract(resource(list R, A), resource(list R, .List)) => resource(list R, A)
    rule subtract(resource(list R, A), resource(list R, ListItem(B) Rest))
         => subtract(resource(list R, remove(A, B)), resource(list R, Rest))

    syntax Bool ::= Resource "contained_in" Resource [function, functional]

    rule resource(nat, A) contained_in resource(nat, B) => A <=Int B
    rule resource(X:Id, A) contained_in resource(X, B) => A ==K B
        requires X =/=K nat
    rule resource(X.T, A) contained_in resource(X.T, B) => A ==K B

    rule resource(option R, none) contained_in resource(option R, _) => true
    rule resource(option R, some(A)) contained_in resource(option R, none) => false
    rule resource(option Q R, some(A)) contained_in resource(option Q R, some(B))
         => resource(R, A) contained_in resource(R, B)

    rule resource(set R, A) contained_in resource(set R, B) => A <=Set B

    // TODO: These are not efficiently written, but they are correctly written (I hope...)
    rule resource(list R, .List) contained_in resource(list R, _) => true
    rule resource(list R, ListItem(_) _) contained_in resource(list R, .List) => false
    rule resource(list R, ListItem(A) Rest) contained_in resource(list R, B)
         => resource(list R, Rest) contained_in resource(list R, remove(B, A))
         requires A in B
    rule resource(list R, ListItem(A) Rest) contained_in resource(list R, B:List) => false
        requires notBool(A in B)

    // Convert resources: Takes a resource value and converts it to be compatible with the specified type
    //  - e.g., an option => set conversion makes `none` into the empty set and `some(A)` into a singleton containing A
    syntax ResourceVal ::= convert(Resource, BaseType) [function]

    // TODO: How to avoid tedious case analysis?

    // Same resource requires no conversion.
    rule convert(resource(R, V), R) => resource(R, V)

    rule convert(resource(R, V), option Q R) => resource(option Q R, some(V))
    rule convert(resource(R, V), set Q R) => resource(set Q R, SetItem(V))
    rule convert(resource(R, V), list Q R) => resource(list Q R, ListItem(V))

    rule convert(resource(option Q R, none), R) => revert("No value!")
    rule convert(resource(option Q R, some(A)), R) => resource(R, A)

    rule convert(resource(option R, none), set R) => resource(set R, .Set)
    rule convert(resource(option R, some(A)), set R) => resource(set R, SetItem(A))

    rule convert(resource(option R, none), list R) => resource(list R, .List)
    rule convert(resource(option R, some(A)), list R) => resource(list R, ListItem(A))

    rule convert(resource(set Q R, .Set), R) => revert("No value!")
    rule convert(resource(set Q R, SetItem(A)), R) => resource(R, A)
    rule convert(resource(set Q R, SetItem(A) SetItem(B) _), R) => revert("Too many values!")

    rule convert(resource(set R, .Set), option R) => resource(option R, none)
    rule convert(resource(set R, SetItem(A)), option R) => resource(option R, some(A))
    rule convert(resource(set R, SetItem(A) SetItem(B) _), option R) => revert("Too many values!")

    // Nondeterministic, but that's the most reasonable behavior for this conversion.
    rule convert(resource(set R, A), list R) => resource(list R, Set2List(A))

    rule convert(resource(list Q R, .List), R) => revert("No value!")
    rule convert(resource(list Q R, ListItem(A)), R) => resource(R, A)
    rule convert(resource(list Q R, ListItem(A) ListItem(B) _), R) => revert("Too many values!")

    rule convert(resource(list R, .List), option R) => resource(option R, none)
    rule convert(resource(list R, ListItem(A)), option R) => resource(option R, some(A))
    rule convert(resource(list R, ListItem(A) ListItem(B) _), option R) => revert("Too many values!")

    rule convert(resource(list R, A), set R) => resource(set R, List2Set(A))

    // Combine resources: takes two collections of values and makes a single collection.
    syntax ResourceVal ::= combine(ResourceVal, ResourceVal) [function]

    // Error propagation
    rule combine(revert(E), _) => revert(E)
    rule combine(_, revert(E)) => revert(E)

    rule combine(resource(R, A), resource(R, emptySingleton)) => resource(R, A)
    rule combine(resource(nat, A), resource(nat, B)) => resource(nat, A +Int B)
    rule combine(resource(R:Id, A), resource(R, B)) => revert("Destination already full!")
        requires R =/=K nat andBool B =/=K emptySingleton
    rule combine(resource(X.T, A), resource(X.T, B)) => revert("Destination already full!")
        requires B =/=K emptySingleton

    rule combine(resource(option R, A), resource(option R, none)) => resource(option R, A)
    rule combine(resource(option R, none), resource(option R, some(B))) => resource(option R, some(B))
    rule combine(resource(option R, some(A)), resource(option R, some(B))) => revert("Destination already full!")

    rule combine(resource(set R, A:Set), resource(set R, B:Set)) => resource(set R, A B)
    // Combine as `B A` instead of `A B`, because the new values should be **appended**, not prepended.
    rule combine(resource(list R, A:List), resource(list R, B:List)) => resource(list R, B A)

    syntax K ::= put(ResourceVal, StorageLoc)

    rule <k> put(R:Resource, Loc) => . ... </k>
        <storage> ... .Map => Loc |-> R ... </storage>

    syntax Resource ::= defaultValue(Type) [function, functional]

    rule defaultValue(Q nat) => resource(nat, 0)
    rule defaultValue(Q X:Id) => resource(X, emptySingleton)
        requires X =/=K nat
    rule defaultValue(Q X.T) => resource(X.T, emptySingleton)
    rule defaultValue(Q option R) => resource(option R, none)
    rule defaultValue(Q set R) => resource(set R, .Set)
    rule defaultValue(Q list R) => resource(list R, .List)
    rule defaultValue(Q:TypeQuant (T1 ~~> T2)) => resource(list T2, .List)

    // =================================
    // Transaction calls:
    // =================================
    syntax K ::= setupArgs(Exprs, VarDefs) [function]

    rule setupArgs(.Exprs, .VarDefs) => .
    rule setupArgs((E:Storage, Es):Exprs, (Y : T, Defs2)) => (var Y : T) ~> (E --> Y) ~> setupArgs(Es, Defs2)

    syntax K ::= cleanEnv(Set)

    rule <k> cleanEnv(ToRemove) => . ... </k>
        <localTypeEnv> Env => removeAll(Env, ToRemove) </localTypeEnv>
        <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup>

    rule <k> X.T(ActualArgs) => setupArgs(ActualArgs, FormalArgs) ~> cleanEnv(keys(Env)) ~> doUnpack((T |-> TxLoc) Fs) ~> S ~> pack(Old, (X |-> XLoc) Lookup, Env) ... </k>
        <lookup> ((X |-> XLoc) Lookup) </lookup>
        <storage> ... XLoc |-> resource(C, (T |-> TxLoc) Fs) ... </storage>
        <transactions> ... C.T |-> transaction(RetType, FormalArgs, S) ... </transactions>
        <fields> ... C |-> Fields </fields>
        <localTypeEnv> Env </localTypeEnv>
        <currentContract> Old => C </currentContract>
        <transformerStack> .List => ListItem(TxLoc) ... </transformerStack>

    // TODO: Move everything to an activation stack system probably so the K-cell becomes more managable?
    rule <k> return Ret ~> _ ~> pack(Old, Lookup, Env) => resolveStorage(Ret) ~> resolveStorage(Loc) ~> selector(everything) ~> pack(Old, Lookup, Env) ... </k>
        <transformerStack> ListItem(Loc) => .List ... </transformerStack>

    // ============================
    // New contract
    // ============================
    syntax K ::= initFields(StorageLoc, Set)

    rule initFields(Loc, .Set) => .
    rule <k> initFields(Loc, SetItem(X : T) Rest) => initFields(Loc, Rest) ... </k>
        <storage>
            ...
            (Loc |-> resource(C, Fs))
            =>
            (Loc |-> resource(C, (X |-> !XLoc:StorageLoc) Fs))
            (!XLoc |-> defaultValue(T))
            ...
        </storage>

    // Pack/unpack
    syntax K ::= pack(QualifiedId, Map, Map)
               | unpack(StorageLoc)
               | doUnpack(Map)

    rule <k> unpack(Loc) => doUnpack(Fs) ... </k>
        <storage> ... Loc |-> resource(C, Fs) ... </storage>

    rule doUnpack(.Map) => .
    rule <k> doUnpack((X |-> Loc) Rest) => doUnpack(Rest) ... </k>
        <lookup> ... .Map => this.X |-> Loc ... </lookup>

    // NOTE: This would be unsafe if used to destroy assets, but the typechecker will ensure that it's safe, so we don't need to check.
    // NOTE: We don't **HAVE** to clean up the storage.
    //       It would be (a little) faster if we didn't, but it does save us from some junk lying around from local variables, which
    //       is probably faster overall, but most importantly, it makes the output nicer to read.
    rule <k> pack(Cls, Lookup, Env) => . ... </k>
        <localTypeEnv> .Map => Env </localTypeEnv>
        <lookup> _ => Lookup </lookup>
        <currentContract> _ => Cls </currentContract>

    rule <k> pack(_, _, _) ... </k>
        <localTypeEnv> ... X |-> _ => .Map ... </localTypeEnv>
        <lookup> ... X |-> Loc:StorageLoc ... </lookup>
        <storage> Store => removeAll(Store, SetItem(Loc)) </storage>
endmodule

