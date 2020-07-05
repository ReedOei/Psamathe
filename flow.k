require "substitution.k"
require "flow-common.k"

module FLOW
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS
    imports SUBSTITUTION

    syntax ErrorVal ::= revert(String)
    syntax ContractVal ::= contract(QualifiedId, Storage)
    syntax Val ::= Set
                 | List
                 | some(Val)
                 | "none" [token]
                 // This can be stored in the middle of a transaction, but not at the end, unless the reference is temporary.
                 | "emptySingleton" [token]
                 | ContractVal
    syntax StorageLoc ::= loc(Int) [freshGenerator, function, functional]
    syntax KResult ::= Val
                     | ErrorVal
                     | Vals
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
        <currentContract> contract(NoContract, #null) </currentContract>
        <activations> .Set </activations>
        <returnValueStack> .List </returnValueStack>

    syntax Resource ::= resource(Type, Val)
    syntax ResourceVal ::= Resource
                         | ErrorVal

    syntax K ::= select(Selector, Resource, Storage, Storage)
               | flow(ResourceVal, Storage)

    syntax K ::= TypeMod

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    rule pass => .

    // Temporary variable declaration
    rule <k> var X : T => . ... </k>
        <localTypeEnv> ... .Map => X |-> canonicalize(T) </localTypeEnv>
        <lookup> ... .Map => X |-> !Loc:StorageLoc </lookup>

    // Simple arithmetic and boolean expressions
    rule I1 + I2 => I1 +Int I2
    rule I1 - I2 => I1 -Int I2

    rule I1:Int = I2:Int => I1 ==Int I2
    rule S1:String = S2:String => S1 ==String S2

    rule I1 < I2 => I1 <Int I2
    rule I1 <= I2 => I1 <=Int I2

    rule true and B => B
    rule false and B => false
    rule true or B => true
    rule false or B => B
    rule not true => false
    rule not false => true

    rule if true then A else B => A
    rule if false then A else B => B

    // =================================
    // Flows:
    // =================================

    // Primitive flows
    rule I:Int --[ everything ]-> D => flow(resource(one nat, I), D)
    rule Str:String --[ everything ]-> D => flow(resource(one string, Str), D)
    rule contract(C, S) --[ everything ]-> D => flow(resource(one C, contract(C, S)), D)

    rule A --[ nothing ]-> B => .

    rule <k> S --[ Sel ]-> D => select(Sel, SV, S, D) ... </k>
        <lookup> ... S |-> Loc ... </lookup>
        <storage> ... Loc |-> SV => .Map ... </storage>

    // Select
    // TODO: Handle more selectors (i.e., quantified and set/list selectors)
    rule select(everything, resource(R, V), S, D)
         =>
         select(V, resource(R, V), S, D)

    rule select(N:Int, resource(one nat, V), S, D)
         =>
         flow(resource(one nat, V -Int N), S) ~> flow(resource(one nat, N), D)
        requires V >=Int N

    rule select(Val, resource(one R, Val), S, D)
         =>
         flow(resource(empty R, emptySingleton), S) ~> flow(resource(one R, Val), D)
        requires R =/=K nat

    rule select(Val, resource(set R, SetItem(Val) Rest), S, D)
         =>
         flow(resource(set R, Rest), S) ~> flow(resource(one R, Val), D)

    rule select(Val, resource(option R, some(Val)), S, D)
         =>
         flow(resource(option R, none), S) ~> flow(resource(one R, some(Val)), D)

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

    // Reduce this case to the case we already handled above
    rule <k> flow(_, S:QualifiedId) ... </k>
        <lookup> ... S |-> Loc ... </lookup>
        <storage> Store => Store (Loc |-> defaultValue(T)) </storage>
        <localTypeEnv> ... S |-> T ... </localTypeEnv>
        requires notBool(Loc in keys(Store))

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

    rule <k> call X.T(ActualArgs) asserting E => setupArgs(ActualArgs, FormalArgs) ~> unpack(ContractStorage, Fields) ~> S ~> pack(Old, Lookup, Env) ~> assert(E) ... </k>
        <transactions> ... C.T |-> transaction(RetType, FormalArgs, S) ... </transactions>
        <localTypeEnv> Env => .Map </localTypeEnv>
        <lookup> Lookup => .Map </lookup>
        <storage> ... Lookup[X] |-> resource(one C, contract(C, ContractStorage)) ... </storage>
        <currentContract> Old => contract(C, ContractStorage) </currentContract>
        <fields> ... C |-> Fields </fields>

    syntax K ::= assert(Expr)
               | assertTrue(Expr) [strict]

    // TODO: Move everything to an activation stack system probably so the K-cell becomes more managable?
    rule <k> return V:Val ~> _ ~> pack(Old, Lookup, Env) ~> assert(E) => pack(Old, Lookup, Env) ~> assert(E) ... </k>
        <returnValueStack> .List => ListItem(V) ... </returnValueStack>

    rule <k> assert(E) => assertTrue(E[result |-> V]) ... </k>
        <returnValueStack> ListItem(V) => .List ... </returnValueStack>

    // TODO: Handle the case that they're not equal by reverting
    rule assertTrue(true) => .
    rule assertTrue(V:Val) => revert("Assertion not true")
        requires V =/=K true

    // ============================
    // New contract
    // ============================
    syntax K ::= initFields(Storage, Set)

    rule <k> new C(Args) --[ Sel ]-> D
             =>
             setupArgs(Args, FormalArgs) ~> initFields(!New:QualifiedId, Fields) ~> unpack(!New, Fields) ~> S ~> pack(Old, Lookup, Env) ~> contract(C, !New) --[ Sel ]-> D
             ...
         </k>
        <fields> ... C |-> Fields ... </fields>
        <constructors> ... C |-> constructor(FormalArgs, S) ... </constructors>
        <localTypeEnv> Env => .Map </localTypeEnv>
        <currentContract> Old => contract(C, !New) </currentContract>
        <lookup> Lookup => .Map </lookup>

    rule initFields(S, .Set) => .
    rule <k> initFields(S, SetItem(X : T) Rest) => initFields(S, Rest) ... </k>
        <storage> ... .Map => S.X |-> defaultValue(T) ... </storage>

    // Pack/unpack
    syntax K ::= pack(ContractVal, Map, Map)
               | unpack(Storage, Set)

    rule unpack(S, .Set) => .
    rule <k> unpack(S, SetItem(X : T) Rest) => unpack(S, Rest) ... </k>
        <lookup> ... .Map => this.X |-> S.X ... </lookup>

    rule <k> pack(Old, Lookup, Env) => . ... </k>
        <lookup> _ => Lookup </lookup>
        <localTypeEnv> .Map => Env </localTypeEnv>
        <currentContract> _ => Old </currentContract>

    // NOTE: This would be unsafe if used to destroy assets, but the typechecker will ensure that it's safe, so we don't need to check.
    // NOTE/TODO: We don't **HAVE** to clean up the storage.
    //       It would be faster if we didn't, but it does save us from some junk lying around from local variables.
    rule <k> pack(Old, Lookup, Env) ... </k>
        <localTypeEnv> ... (X |-> T) => .Map ... </localTypeEnv>
        // TODO: Loc may be something like freshStorage(N).FieldName instead of a StorageLoc
        //      However, this should be fine, as we will never try to clean up something like that,
        //      Because it won't be in the localTypeEnv.
        <lookup> ... (X |-> Loc:StorageLoc) => .Map ... </lookup>
        <storage> ... (Loc |-> V) => .Map ... </storage>
endmodule

