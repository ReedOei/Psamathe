require "substitution.k"
require "flow-common.k"

module FLOW
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS
    imports SUBSTITUTION

    syntax StorageLoc ::= loc(Int) [freshGenerator, function, functional]
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
    syntax Resource ::= resource(Type, BasicVal)
    syntax ResourceVal ::= Resource
                         | ErrorVal
    syntax Expr ::= ResourceVal
    syntax KResult ::= ResourceVal
                     | SpecialSelect
                     | StorageLoc

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
        <activations> .Set </activations>
        <returnValueStack> .List </returnValueStack>

    syntax K ::= select(Selector, Resource, Storage, Storage) [strict(1)]
               | flow(ResourceVal, Storage)

    syntax K ::= TypeMod

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    rule pass => .

    // Temporary variable declaration
    rule <k> var X : T => . ... </k>
        <localTypeEnv> ... .Map => X |-> canonicalize(T) </localTypeEnv>
        <lookup> ... .Map => X |-> !Loc:StorageLoc </lookup>
        <storage> ... .Map => !Loc |-> defaultValue(canonicalize(T)) ... </storage>

    rule I:Int => resource(one nat, I)
        requires I >=Int 0

    rule B:Bool => resource(one bool, B)

    rule S:String => resource(one string, S)

    // Simple arithmetic and boolean expressions
    // TODO: I would like to remove all this resource stuff at some point
    //       The typechecker can also compile this stuff into the correct instructions to permit erasing all these runtime types.
    rule resource(one nat, I1) + resource(one nat, I2) => resource(one nat, I1 +Int I2)
    rule resource(one nat, I1) - resource(one nat, I2) => resource(one nat, I1 -Int I2)

    rule resource(R, A) = resource(R, B) => A ==K B

    rule resource(one nat, I1) < resource(one nat, I2) => resource(one bool, I1 <Int I2)
    rule resource(one nat, I1) <= resource(one nat, I2) => resource(one bool, I1 <=Int I2)

    rule resource(one bool, true) and B => B
    rule resource(one bool, false) and B => resource(one bool, false)
    rule resource(one bool, true) or B => resource(one bool, true)
    rule resource(one bool, false) or B => B
    rule not resource(one bool, B) => notBool B

    rule if resource(one bool, true) then A else B => A
    rule if resource(one bool, false) then A else B => B

    // Variable lookup
    rule <k> X => demote(V) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... Loc |-> V ... </storage>

    // TODO: Finish this
    syntax K ::= demote(Resource)

    rule demote(resource(one nat, V)) => resource(one nat, V)

    // =================================
    // Flows:
    // =================================

    // Primitive flows
    rule I:Int --[ everything ]-> D => flow(resource(one nat, I), D)
    rule Str:String --[ everything ]-> D => flow(resource(one string, Str), D)

    rule A --[ nothing ]-> B => .

    rule <k> S --[ Sel ]-> D => select(Sel, SV, S, D) ... </k>
        <lookup> ... S |-> Loc ... </lookup>
        <storage> ... Loc |-> SV => .Map ... </storage>

    // Select
    // TODO: Handle more selectors (i.e., quantified and set/list selectors)
    rule select(everything, resource(R, V), S, D)
         =>
         select(resource(R, V), resource(R, V), S, D)

    rule select(resource(one nat, N), resource(one nat, V), S, D)
         =>
         put(resource(one nat, V -Int N), S) ~> flow(resource(one nat, N), D)
        requires V >=Int N

    rule select(resource(one R, Val), resource(one R, Val), S, D)
         =>
         put(resource(empty R, emptySingleton), S) ~> flow(resource(one R, Val), D)
        requires R =/=K nat

    rule select(resource(one R, Val), resource(set R, SetItem(Val) Rest), S, D)
         =>
         put(resource(set R, Rest), S) ~> flow(resource(one R, Val), D)

    rule select(resource(one R, Val), resource(option R, some(Val)), S, D)
         =>
         put(resource(option R, none), S) ~> flow(resource(one R, some(Val)), D)

    // Convert resources: Takes a resource value and converts it to be compatible with the specified type
    //  - e.g., an option => set conversion makes `none` into the empty set and `some(A)` into a singleton containing A
    syntax ResourceVal ::= convert(Resource, Type) [function]

    // TODO: How to avoid tedious case analysis?

    // Same resource requires no conversion.
    rule convert(resource(R, V), R) => resource(R, V)

    // Ugly special conversion rule---this lets us fill empty storages.
    rule convert(resource(one R, V), empty R) => resource(one R, V)

    rule convert(resource(one R, V), option R) => resource(option R, some(V))
    rule convert(resource(one R, V), set R) => resource(set R, SetItem(V))
    rule convert(resource(one R, V), list R) => resource(option R, some(V))

    rule convert(resource(option R, none), one R) => revert("No value!")
    rule convert(resource(option R, some(A)), one R) => resource(one R, A)

    rule convert(resource(option R, none), set R) => resource(set R, .Set)
    rule convert(resource(option R, some(A)), set R) => resource(set R, SetItem(A))

    rule convert(resource(option R, none), list R) => resource(set R, .List)
    rule convert(resource(option R, some(A)), list R) => resource(set R, ListItem(A))

    rule convert(resource(set R, .Set), one R) => revert("No value!")
    rule convert(resource(set R, SetItem(A)), one R) => resource(one R, A)
    rule convert(resource(set R, SetItem(A) SetItem(B) _), one R) => revert("Too many values!")

    rule convert(resource(set R, .Set), option R) => resource(option R, none)
    rule convert(resource(set R, SetItem(A)), option R) => resource(option R, some(A))
    rule convert(resource(set R, SetItem(A) SetItem(B) _), option R) => revert("Too many values!")

    // Nondeterministic, but that's the most reasonable behavior for this conversion.
    rule convert(resource(set R, A), list R) => resource(list R, Set2List(A))

    rule convert(resource(list R, .List), one R) => revert("No value!")
    rule convert(resource(list R, ListItem(A)), one R) => resource(one R, A)
    rule convert(resource(list R, ListItem(A) ListItem(B) _), one R) => revert("Too many values!")

    rule convert(resource(list R, .List), option R) => resource(option R, none)
    rule convert(resource(list R, ListItem(A)), option R) => resource(option R, some(A))
    rule convert(resource(list R, ListItem(A) ListItem(B) _), option R) => revert("Too many values!")

    rule convert(resource(list R, A), set R) => resource(set R, List2Set(A))

    // Combine resources: takes two collections of values and makes a single collection.
    syntax ResourceVal ::= combine(ResourceVal, ResourceVal) [function]

    // Error propagation
    rule combine(revert(E), _) => revert(E)
    rule combine(_, revert(E)) => revert(E)

    rule combine(resource(one R, A), resource(empty R, emptySingleton)) => resource(one R, A)
    rule combine(resource(one nat, A), resource(one nat, B)) => resource(one nat, A +Int B)
    rule combine(resource(one R, A), resource(one R, B)) => revert("Destination already full!")
        requires R =/=K nat

    rule combine(resource(option R, A), resource(option R, none)) => resource(option R, A)
    rule combine(resource(option R, none), resource(option R, some(B))) => resource(option R, some(B))
    rule combine(resource(option R, some(A)), resource(option R, some(B))) => revert("Destination already full!")

    rule combine(resource(set R, A:Set), resource(set R, B:Set)) => resource(set R, A B)
    // Combine as `B A` instead of `A B`, because the new values should be **appended**, not prepended.
    rule combine(resource(list R, A:List), resource(list R, B:List)) => resource(list R, B A)

    // Flow resolution
    rule <k> flow(resource(R1, V), S) => put(combine(convert(resource(R1, V), R2), resource(R2, Cur)), S) ... </k>
        <lookup> ... S |-> Loc ... </lookup>
        <storage> ... (Loc |-> resource(R2, Cur)) => .Map ... </storage>

    rule <k> flow(resource(R, V), consume) => checkConsumable(R) ... </k>

    syntax K ::= put(ResourceVal, Storage)

    rule <k> put(R:Resource, S) => . ... </k>
        <lookup> ... S |-> Loc ... </lookup>
        <storage> ... .Map => Loc |-> R ... </storage>

    syntax Resource ::= defaultValue(Type) [function]

    rule defaultValue(one nat) => resource(one nat, 0)
    rule defaultValue(one R) => resource(empty R, emptySingleton)
        requires R =/=K nat
    rule defaultValue(option R) => resource(set R, none)
    rule defaultValue(set R) => resource(set R, .Set)
    rule defaultValue(list R) => resource(set R, .List)

    // =================================
    // Actions:
    // =================================

    // Action sequencing
    rule .Actions => . [structural]
    rule A1:Action As:Actions => A1 ~> As [structural]

    // Externals calls:
    syntax K ::= setupArgs(Exprs, VarDefs) [function]

    rule setupArgs(.Exprs, .VarDefs) => .
    rule setupArgs((E:Storage, Es), (Y : T, Defs2)) => (var Y : T) ~> (E --> Y) ~> setupArgs(Es, Defs2)

    syntax K ::= cleanEnv(Set)

    rule <k> cleanEnv(ToRemove) => . ... </k>
        <localTypeEnv> Env => removeAll(Env, ToRemove) </localTypeEnv>
        <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup>

    rule <k> call X.T(ActualArgs) asserting E => setupArgs(ActualArgs, FormalArgs) ~> cleanEnv(keys(Env)) ~> doUnpack(Fs) ~> S ~> pack(Old, (X |-> XLoc) Lookup, Env) ~> assert(E) ... </k>
        <lookup> ((X |-> XLoc) Lookup) </lookup>
        <storage> ... XLoc |-> resource(one C, Fs) ... </storage>
        <transactions> ... C.T |-> transaction(RetType, FormalArgs, S) ... </transactions>
        <fields> ... C |-> Fields </fields>
        <localTypeEnv> Env </localTypeEnv>
        <currentContract> Old => C </currentContract>

    syntax K ::= assert(Expr)
               | assertTrue(Expr) [strict]

    // TODO: Move everything to an activation stack system probably so the K-cell becomes more managable?
    rule <k> return resource(R, V) ~> _ ~> pack(Old, Lookup, Env) ~> assert(E) => pack(Old, Lookup, Env) ~> assert(E) ... </k>
        <returnValueStack> .List => ListItem(resource(R, V)) ... </returnValueStack>

    rule <k> assert(E) => assertTrue(E[result |-> V]) ... </k>
        <returnValueStack> ListItem(V) => .List ... </returnValueStack>

    // TODO: Handle the case that they're not equal by reverting
    rule assertTrue(resource(one bool, true)) => .
    rule assertTrue(resource(one bool, false)) => revert("Assertion not true")

    // ============================
    // New contract
    // ============================
    syntax K ::= initFields(StorageLoc, Set)

    rule <k> new C(Args) --[ Sel ]-> D
             =>
             initFields(!Loc:StorageLoc, Fields) ~> setupArgs(Args, FormalArgs) ~> cleanEnv(keys(Env)) ~> unpack(!Loc) ~> S ~> pack(Old, Lookup (!Fresh:QualifiedId |-> !Loc), Env) ~> !Fresh --[ Sel ]-> D
             ...
         </k>
        <storage> ... .Map => !Loc |-> resource(one C, .Map) ... </storage>
        <localTypeEnv> Env </localTypeEnv>
        <lookup> Lookup </lookup>
        <currentContract> Old => C </currentContract>
        <fields> ... C |-> Fields ... </fields>
        <constructors> ... C |-> constructor(FormalArgs, S) ... </constructors>

    rule initFields(Loc, .Set) => .
    rule <k> initFields(Loc, SetItem(X : T) Rest) => initFields(Loc, Rest) ... </k>
        <storage>
            ...
            (Loc |-> resource(one C, Fs))
            =>
            (Loc |-> resource(one C, (X |-> !XLoc:StorageLoc) Fs))
            (!XLoc |-> defaultValue(T))
            ...
        </storage>

    // Pack/unpack
    syntax K ::= pack(QualifiedId, Map, Map)
               | unpack(StorageLoc)
               | doUnpack(Map)

    rule <k> unpack(Loc) => doUnpack(Fs) ... </k>
        <storage> ... Loc |-> resource(one C, Fs) ... </storage>

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

    rule <k> pack(Cls, Lookup, Env) ... </k>
        <localTypeEnv> ... X |-> T => .Map ... </localTypeEnv>
        <lookup> ... X |-> Loc:StorageLoc ... </lookup>
        <storage> Store => removeAll(Store, SetItem(Loc)) </storage>
endmodule

