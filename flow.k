require "flow-common.k"

module FLOW
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS

    syntax StorageLoc ::= loc(Int) [freshGenerator]
    /* syntax SpecialStorage ::= StorageLoc */
    /*                         | literal(Resource) */
    /*                         | contract(Resource, Exprs) [strict(2), result(Resource)] */
    syntax BasicVal ::= Int
                      | Bool
                      | String
                      | Set
                      | List
                      | Map
                      | EmptyVal
    syntax Val ::= resource(BaseType, BasicVal)
    syntax KResult ::= Val | Vals

    syntax Var ::= "NoContract"

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
    rule pass => . [structural]

    // Temporary variable declaration
    rule <k> var X : T := V in S:Stmt => S ~> drop(X) ... </k>
        <localTypeEnv> ... .Map => X |-> T ... </localTypeEnv>
        <lookup> ... .Map => X |-> !Loc:StorageLoc ... </lookup>
        <storage> ... .Map => !Loc |-> V ... </storage>
        requires resource(_, emptyval) :/=K V

    syntax Stmt ::= drop(Var)
    rule <k> drop(X) => . ... </k>
        <localTypeEnv> ... X |-> T => .Map ... </localTypeEnv>
        <lookup> ... X |-> Loc => .Map ... </lookup>
        <storage> ... Loc |-> R => .Map ... </storage>

    /* // Check-In */
    /* rule Sel in R => checkIn(Sel, resolveStorage(R)) */

    /* syntax Expr ::= checkIn(SelectorVal, Storage) [strict(2), result(SpecialStorage)] */

    /* rule <k> checkIn(Sel, Loc) => resource(bool, select(Sel, SV) contained_in SV) ... </k> */
    /*     <storage> ... Loc |-> SV ... </storage> */

    /* // Literals */
    /* rule I:Int => resource(nat, I) */
    /*     requires I >=Int 0 */
    /* rule B:Bool => resource(bool, B) */
    /* rule S:String => resource(string, S) */

    /* // Simple arithmetic and boolean expressions */
    /* // TODO: I would like to remove all this resource stuff at some point */
    /* //       The typechecker can also compile this stuff into the correct instructions to permit erasing all these runtime types. */
    /* rule resource(nat, I1) + resource(nat, I2) => resource(nat, I1 +Int I2) */
    /* rule resource(nat, I1) - resource(nat, I2) => resource(nat, I1 -Int I2) */

    /* rule resource(R, A) = resource(R, B) => A ==K B */

    /* rule resource(nat, I1) < resource(nat, I2) => resource(bool, I1 <Int I2) */
    /* rule resource(nat, I1) <= resource(nat, I2) => resource(bool, I1 <=Int I2) */

    /* rule resource(bool, true) and B => B */
    /* rule resource(bool, false) and _ => resource(bool, false) */
    /* rule resource(bool, true) or _ => resource(bool, true) */
    /* rule resource(bool, false) or B => B */
    /* rule not resource(bool, B) => resource(bool, notBool B) */

    /* rule if resource(bool, true) { A } else { _ }  => A */
    /* rule if resource(bool, false) { _ } else { B } => B */

    /* // Variable lookup */
    /* rule <k> X => demoteVal(Val) ... </k> */
    /*     <lookup> ... X |-> Loc ... </lookup> */
    /*     <storage> ... Loc |-> Val ... </storage> */

    /* rule <k> X . F => demoteVal(Val) ... </k> */
    /*     <lookup> ... X |-> XLoc ... </lookup> */
    /*     <storage> ... (XLoc |-> resource(_, (F |-> Loc) _)) (Loc |-> Val) ... </storage> */

    /* syntax Storage ::= resolveStorage(Storage) */

    /* // NOTE: Some unfortunate duplication here... */
    /* rule resolveStorage(I:Int) => resolveStorage(resource(nat, I)) */
    /*     requires I >=Int 0 */
    /* rule resolveStorage(S:String) => resolveStorage(resource(string, S)) */
    /* rule resolveStorage(B:Bool) => resolveStorage(resource(bool, B)) */
    /* rule resolveStorage(resource(R, V)) => literal(resource(R, V)) */
    /* rule resolveStorage(consume) => consume */
    /* rule <k> resolveStorage(new C(Args)) => initFields(resource(C, .Map), Fields, Args) ... </k> */
    /*     <fields> ... C |-> Fields ... </fields> */
    /* rule resolveStorage(Loc:StorageLoc) => Loc */
    /* rule <k> resolveStorage(X) => Loc ... </k> */
    /*     <lookup> ... X |-> Loc ... </lookup> */
    /* rule <k> resolveStorage(X . F) => Loc ... </k> */
    /*     <lookup> ... X |-> XLoc ... </lookup> */
    /*     <storage> ... XLoc |-> resource(R, (F |-> Loc) _) ... </storage> */

    /* // NOTE: All types are always stored as their demoted value, so we simply need to demote the type. */
    /* syntax Resource ::= demoteVal(Resource) [function, functional] */
    /* rule demoteVal(resource(R, V)) => resource(demote(R), V) */

    /* // ================================= */
    /* // Flows: */
    /* // ================================= */
    /* rule S --[ Sel:SelectorVal ]-> D => handleFlow(Sel, resolveStorage(S), resolveStorage(D)) */

    /* syntax Stmt ::= handleFlow(SelectorVal, Storage, Storage) [strict(2,3), result(SpecialStorage)] */

    /* rule <k> handleFlow(Sel, SourceLoc, consume) => . ... </k> */
    /*     <storage> ... (SourceLoc |-> (SV => subtract(SV, select(Sel, SV)))) ... </storage> */
    /*     requires select(Sel, SV) contained_in SV */

    /* // TODO: Do we really need literal()? */
    /* rule <k> handleFlow(Sel, literal(R), D) => put(combine(convert(R, DR), resource(DR, Cur)), D) ...  </k> */
    /*     <storage> ... D |-> resource(DR, Cur) => .Map ... </storage> */

    /* rule <k> handleFlow(Sel, contract(resource(C, Fs), Args), D) */
    /*          => */
    /*          put(combine(resource(C, Fs), DV), D) */
    /*          ~> */
    /*          setupArgs(Args, FormalArgs, cleanEnv(keys(Env)) S) ~> pack(Old, Lookup, Env) */
    /*          ... */
    /*      </k> */
    /*     <localTypeEnv> Env </localTypeEnv> */
    /*     <storage> ... D |-> DV => .Map ... </storage> */
    /*     <lookup> Lookup </lookup> */
    /*     <currentContract> Old => C </currentContract> */
    /*     <constructors> ... C |-> constructor(FormalArgs, S) ... </constructors> */

    /* rule <k> handleFlow(Sel, SourceLoc, DestLoc) => put(combine(convert(select(Sel, SV), DestR), resource(DestR, Cur)), DestLoc) ... </k> */
    /*     <storage> */
    /*         ... */
    /*         (SourceLoc |-> SV) */
    /*         (DestLoc |-> resource(DestR, Cur)) */
    /*         => */
    /*         (SourceLoc |-> subtract(SV, select(Sel, SV))) */
    /*         ... */
    /*     </storage> */
    /*     requires select(Sel, SV) contained_in SV */

    /* syntax Resource ::= select(SelectorVal, Resource) [function, functional] */

    /* // Selection (includes select, subtract, and contains) */
    /* // TODO: Handle selectors that need to be converted (or maybe just convert by default), such as selecting from a set with a list. */
    /* rule select(everything, R) => R */
    /* rule select(resource(R, V), resource(R, _)) => resource(R, V) */
    /* rule select(resource(R, V), resource(option Q R, _)) => resource(option Q R, some(V)) */
    /* rule select(resource(R, V), resource(set Q R, _)) => resource(set Q R, SetItem(V)) */
    /* rule select(resource(R, V), resource(list Q R, _)) => resource(list Q R, ListItem(V)) */

    /* syntax Resource ::= subtract(Resource, Resource) [function, functional] */

    /* rule subtract(resource(nat, A), resource(nat, B)) => resource(nat, A -Int B) */
    /* rule subtract(resource(X:Var, A), resource(X, A)) => resource(X, emptyval) */
    /*     requires X =/=K nat */
    /* rule subtract(resource(X.T, A), resource(X.T, A)) => resource(X.T, emptyval) */
    /* rule subtract(resource(X.T, A), resource(X.T, A)) => resource(X.T, emptyval) */
    /* rule subtract(resource(T1 * T2, A), resource(T1 * T2, A)) => resource(T1 * T2, emptyval) */

    /* rule subtract(resource(option R, A), resource(option R, none)) => resource(option R, A) */
    /* rule subtract(resource(option R, some(A)), resource(option R, some(A))) => resource(option R, none) */

    /* rule subtract(resource(set R, A), resource(set R, B)) => resource(set R, A -Set B) */

    /* rule subtract(resource(list R, A), resource(list R, .List)) => resource(list R, A) */
    /* rule subtract(resource(list R, A), resource(list R, ListItem(B) Rest)) */
    /*      => subtract(resource(list R, remove(A, B)), resource(list R, Rest)) */

    /* rule subtract(resource(R, A), resource(S, _)) => resource(R, A) */
    /*     requires R =/=K S */

    /* syntax Bool ::= Resource "contained_in" Resource [function, functional] */

    /* rule resource(nat, A) contained_in resource(nat, B) => A <=Int B */
    /* rule resource(X:Var, A) contained_in resource(X, B) => A ==K B */
    /*     requires X =/=K nat */
    /* rule resource(X.T, A) contained_in resource(X.T, B) => A ==K B */

    /* rule resource(option R, none) contained_in resource(option R, _) => true */
    /* rule resource(option R, some(A)) contained_in resource(option R, none) => false */
    /* rule resource(option Q R, some(A)) contained_in resource(option Q R, some(B)) */
    /*      => resource(R, A) contained_in resource(R, B) */

    /* rule resource(set R, A) contained_in resource(set R, B) => A <=Set B */

    /* // TODO: These are not efficiently written, but they are correctly written (I hope...) */
    /* rule resource(list R, .List) contained_in resource(list R, _) => true */
    /* rule resource(list R, ListItem(_) _) contained_in resource(list R, .List) => false */
    /* rule resource(list R, ListItem(A) Rest) contained_in resource(list R, B) */
    /*      => */
    /*      (A in B) andBool (resource(list R, Rest) contained_in resource(list R, remove(B, A))) */

    /* rule resource(T1 * T2, V1) contained_in resource(T1 * T2, V2) => V1 ==K V2 */

    /* rule resource(_, _) contained_in resource(T1 ~~> T2, _) => false */
    /* rule resource(T1 ~~> T2, _) contained_in resource(_, _) => false */

    /* // Convert resources: Takes a resource value and converts it to be compatible with the specified type */
    /* //  - e.g., an option => set conversion makes `none` into the empty set and `some(A)` into a singleton containing A */
    /* syntax ResourceVal ::= convert(Resource, BaseType) [function, functional] */

    /* // TODO: How to avoid tedious case analysis? */

    /* // Same resource requires no conversion. */
    /* rule convert(resource(R, V), R) => resource(R, V) */

    /* rule convert(resource(R, V), option Q R) => resource(option Q R, some(V)) */
    /* rule convert(resource(R, V), set Q R) => resource(set Q R, SetItem(V)) */
    /* rule convert(resource(R, V), list Q R) => resource(list Q R, ListItem(V)) */

    /* rule convert(resource(option _ R, none), R) => revert("No value!") */
    /* rule convert(resource(option _ R, some(A)), R) => resource(R, A) */

    /* rule convert(resource(option R, none), set R) => resource(set R, .Set) */
    /* rule convert(resource(option R, some(A)), set R) => resource(set R, SetItem(A)) */

    /* rule convert(resource(option R, none), list R) => resource(list R, .List) */
    /* rule convert(resource(option R, some(A)), list R) => resource(list R, ListItem(A)) */

    /* rule convert(resource(set _ R, .Set), R) => revert("No value!") */
    /* rule convert(resource(set _ R, SetItem(A)), R) => resource(R, A) */
    /* rule convert(resource(set _ R, SetItem(A) SetItem(B) _), R) => revert("Too many values!") */

    /* rule convert(resource(set R, .Set), option R) => resource(option R, none) */
    /* rule convert(resource(set R, SetItem(A)), option R) => resource(option R, some(A)) */
    /* rule convert(resource(set R, SetItem(_) SetItem(_) _), option R) => revert("Too many values!") */

    /* // Nondeterministic, but that's the most reasonable behavior for this conversion. */
    /* rule convert(resource(set R, A), list R) => resource(list R, Set2List(A)) */

    /* rule convert(resource(list _ R, .List), R) => revert("No value!") */
    /* rule convert(resource(list _ R, ListItem(A)), R) => resource(R, A) */
    /* rule convert(resource(list _ R, ListItem(_) ListItem(_) _), R) => revert("Too many values!") */

    /* rule convert(resource(list R, .List), option R) => resource(option R, none) */
    /* rule convert(resource(list R, ListItem(A)), option R) => resource(option R, some(A)) */
    /* rule convert(resource(list R, ListItem(_) ListItem(_) _), option R) => revert("Too many values!") */

    /* rule convert(resource(list R, A), set R) => resource(set R, List2Set(A)) */

    /* // Combine resources: takes two collections of values and makes a single collection. */
    /* syntax ResourceVal ::= combine(ResourceVal, ResourceVal) [function, functional] */

    /* // Error propagation */
    /* rule combine(revert(E), _) => revert(E) */
    /* rule combine(_, revert(E)) => revert(E) */

    /* rule combine(resource(R, A), resource(R, emptyval)) => resource(R, A) */
    /* rule combine(resource(nat, A), resource(nat, B)) => resource(nat, A +Int B) */
    /* rule combine(resource(X:Var, _), resource(_, B)) => revert("Destination already full!") */
    /*     requires X =/=K nat andBool B =/=K emptyval */
    /* rule combine(resource(X.T, _), resource(X.T, B)) => revert("Destination already full!") */
    /*     requires B =/=K emptyval */
    /* rule combine(resource(T1 * T2, _), resource(T1 * T2, B)) => revert("Destination already full!") */
    /*     requires B =/=K emptyval */

    /* rule combine(resource(option R, A), resource(option R, none)) => resource(option R, A) */
    /* rule combine(resource(option R, none), resource(option R, some(B))) => resource(option R, some(B)) */
    /* rule combine(resource(option R, some(_)), resource(option R, some(B))) => revert("Destination already full!") */

    /* rule combine(resource(set R, A:Set), resource(set R, B:Set)) => resource(set R, A B) */
    /* // Combine as `B A` instead of `A B`, because the new values should be **appended**, not prepended. */
    /* rule combine(resource(list R, A:List), resource(list R, B:List)) => resource(list R, B A) */

    /* syntax Stmt ::= put(ResourceVal, StorageLoc) */

    /* rule <k> put(R:Resource, Loc) => . ... </k> */
    /*     <storage> ... .Map => Loc |-> R ... </storage> */

    /* syntax Resource ::= defaultValue(Type) [function, functional] */

    /* rule defaultValue(_ nat) => resource(nat, 0) */
    /* rule defaultValue(_ X:Var) => resource(X, emptyval) */
    /*     requires X =/=K nat */
    /* rule defaultValue(_ X.T) => resource(X.T, emptyval) */
    /* rule defaultValue(_:TypeQuant (T1 * T2)) => resource(T1 * T2, emptyval) */
    /* rule defaultValue(_ option R) => resource(option R, none) */
    /* rule defaultValue(_ set R) => resource(set R, .Set) */
    /* rule defaultValue(_ list R) => resource(list R, .List) */
    /* rule defaultValue(_:TypeQuant (T1 ~~> T2)) => resource(list T2, .List) */

    /* // ================================= */
    /* // Transaction calls: */
    /* // ================================= */
    /* syntax Stmt ::= setupArgs(Exprs, VarDefs, Stmt) */

    /* rule setupArgs(.Exprs, .VarDefs, S) => S */
    /* rule setupArgs((E:Storage, Es):Exprs, (Y : T, Defs2), S) => var Y : T := E in setupArgs(Es, Defs2, S) */

    /* syntax Stmt ::= cleanEnv(Set) */

    /* rule <k> cleanEnv(ToRemove) => . ... </k> */
    /*     <localTypeEnv> Env => removeAll(Env, ToRemove) </localTypeEnv> */
    /*     <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup> */

    /* rule <k> X.T(ActualArgs) => setupArgs(ActualArgs, FormalArgs, cleanEnv(keys(Env)) S) ~> pack(Old, (X |-> XLoc) Lookup, Env) ... </k> */
    /*     <lookup> ((X |-> XLoc) Lookup) </lookup> */
    /*     <storage> ... XLoc |-> resource(C, (T |-> TxLoc) Fs) ... </storage> */
    /*     <transactions> ... C.T |-> transaction(RetType, FormalArgs, S) ... </transactions> */
    /*     <fields> ... C |-> Fields </fields> */
    /*     <localTypeEnv> Env </localTypeEnv> */
    /*     <currentContract> Old => C </currentContract> */
    /*     <transformerStack> .List => ListItem(TxLoc) ... </transformerStack> */

    /* // TODO: Move everything to an activation stack system probably so the K-cell becomes more managable? */
    /* // TODO: Convert all returns to a flow to the return variable and add if statements and such so that we immediately jump to the end. */
    /* rule <k> return Ret ~> _ ~> pack(Old, Lookup, Env) => handleFlow(everything, resolveStorage(Ret), resolveStorage(Loc)) ~> pack(Old, Lookup, Env) ... </k> */
    /*     <transformerStack> ListItem(Loc) => .List ... </transformerStack> */

    /* // ============================ */
    /* // New contract */
    /* // ============================ */
    /* syntax Storage ::= initFields(Resource, Set, Exprs) */

    /* rule initFields(R, .Set, Args) => contract(R, Args) */
    /* rule <k> initFields(resource(C, Fs), SetItem(X : T) Rest, Args) => initFields(resource(C, (X |-> !XLoc:StorageLoc) Fs), Rest, Args) ... </k> */
    /*     <storage> ... .Map => !XLoc |-> defaultValue(T) ... </storage> */

    /* // Pack TODO: Rename this to something else, because there's also a pack construct in the language itself. */
    /* syntax Stmt ::= pack(Var, Map, Map) */

    /* // NOTE: This would be unsafe if used to destroy assets, but the typechecker will ensure that it's safe, so we don't need to check. */
    /* // NOTE: We don't **HAVE** to clean up the storage. */
    /* //       It would be (a little) faster if we didn't, but it does save us from some junk lying around from local variables, which */
    /* //       is probably faster overall, but most importantly, it makes the output nicer to read. */
    /* rule <k> pack(Cls, Lookup, Env) => . ... </k> */
    /*     <localTypeEnv> .Map => Env </localTypeEnv> */
    /*     <lookup> _ => Lookup </lookup> */
    /*     <currentContract> _ => Cls </currentContract> */

    /* rule <k> pack(_, _, _) ... </k> */
    /*     <localTypeEnv> ... X |-> _ => .Map ... </localTypeEnv> */
    /*     <lookup> ... X |-> Loc:StorageLoc ... </lookup> */
    /*     <storage> Store => removeAll(Store, SetItem(Loc)) </storage> */
endmodule

