requires "pure-flow-common.k"

module PURE-FLOW-SYNTAX
    imports DOMAINS-SYNTAX
    imports PURE-FLOW-COMMON-SYNTAX
endmodule

module PURE-FLOW
    imports DOMAINS
    imports COLLECTIONS

    imports PURE-FLOW-SYNTAX
    imports PURE-FLOW-COMMON

    configuration
        <common />
        <k> $PGM:Program </k>
        <functions> .Map </functions>
        <lookup> .Map </lookup>
        <storage> .Map </storage>
        <catchStack> .List </catchStack>

    syntax Type ::= demoteType(Type) [function, functional]
    rule demoteType(Q:TypeQuant T) => Q demoteBaseType(T)

    syntax StorageLoc ::= loc(Int)
    syntax Resource ::= "error"
                      | resource(BaseType, List)

    // A location(L, V) is a pair of a storage location, where L place that the value V is stored.
    syntax Location ::= location(StorageLoc, Resource)
    syntax Locator ::= List // So that we can use a list of Locations as the result value of a locator.
    syntax KResult ::= List // A list of Locations

    syntax List ::= valueOf(Resource) [function]
    rule valueOf(resource(_, V)) => V

    // =================================
    // Sequence
    // =================================
    rule .Stmts => . [structural]
    rule S1:Stmt Rest:Stmts => S1 ~> Rest [structural]

    // =================================
    // Declarations
    // =================================
    syntax KItem ::= transformer(VarDef, VarDefs, Stmts)

    rule <k> (transformer F(FormalArgs) -> Ret { Body }) Decls ; S => Decls ; S </k>
        <functions> ... .Map => F |-> transformer(Ret, FormalArgs, Body) ... </functions>
        [structural]

    rule .Decls ; S => S [structural]

    // =================================
    // Environment Helpers
    // =================================
    syntax Stmt ::= insert(Var, StorageLoc)
                  | resetEnv(Map)

    rule <k> insert(X, Loc) => . ... </k>
        <lookup> ... .Map => X |-> Loc ... </lookup>
    rule <k> resetEnv(Lookup) => . ... </k>
        <lookup> _ => Lookup </lookup>

    syntax Stmt ::= drop(Var)
                  | dropLoc(StorageLoc)
    rule <k> drop(X) => . ... </k>
        <lookup> ... X |-> _ => .Map ... </lookup>

    rule <k> dropLoc(Loc) => . ... </k>
        <storage> ... Loc |-> _ => .Map ... </storage>

    // =================================
    // Try-Catch:
    // =================================
    // Stores the variable/type to catch, the handler, the lookup table, the storage to restore to, and the continuation.
    syntax Stmt ::= catch(Stmts, Map, Map, K)
                  | "revert"
                  | "dropCatch"

    rule <k> try { S1 } catch { S2 } ~> K => S1 ~> dropCatch ~> K </k>
        <lookup> Lookup </lookup>
        <storage> Storage </storage>
        <catchStack> .List => ListItem(catch(S2, Lookup, Storage, K)) ... </catchStack>

    rule <k> revert ~> _ => S ~> K </k>
        <lookup> _ => Lookup </lookup>
        <storage> _ => Storage </storage>
        <catchStack> ListItem(catch(S, Lookup, Storage, K)) => .List ... </catchStack>

    rule <k> dropCatch => . ... </k>
        <catchStack> ListItem(_) => .List ... </catchStack>

    // ==================================
    // Put:
    // ==================================
    /* syntax Stmt ::= put(Resource, StorageVal) */

    /* rule put(_, consume) => . */
    /* rule <k> put(resource(R, Vs), Loc) => . ... </k> */
    /*     <storage> ... Loc |-> (resource(R, Ws) => combine(resource(R, Ws), resource(R, Vs))) ... </storage> */
    /*     requires combine(resource(R, Ws), resource(R, Vs)) =/=K error */
    /* rule <k> put(resource(R, Vs), Loc) => revert ... </k> */
    /*     <storage> ... Loc |-> resource(R, Ws) ... </storage> */
    /*     requires combine(resource(R, Ws), resource(R, Vs)) ==K error */

    // =================================
    // combine(R1, R2):
    // =================================
    syntax Resource ::= combine(Resource, Resource) [function, functional]

    rule combine(error, _) => error
    rule combine(_, error) => error

    rule combine(resource(bool, ListItem(A)), resource(bool, ListItem(B))) => resource(bool, ListItem(A orBool B))
    rule combine(resource(bool, .List), resource(bool, B)) => resource(bool, B)
    rule combine(resource(bool, A), resource(bool, .List)) => resource(bool, A)

    rule combine(resource(nat, ListItem(A)), resource(nat, ListItem(B))) => resource(nat, ListItem(A +Int B))
    rule combine(resource(nat, .List), resource(nat, B)) => resource(nat, B)
    rule combine(resource(nat, A), resource(nat, .List)) => resource(nat, A)

    rule combine(resource(list R, Ws), resource(list R, Vs)) => resource(list R, Ws Vs)

    rule combine(resource({ Members }, .List), resource({ Members }, FieldLocs)) => resource({ Members }, FieldLocs)
    rule combine(resource({ Members }, FieldLocs), resource({ Members }, .List)) => resource({ Members }, FieldLocs)
    // Can't have combine two records because that would lead to overwriting one of them.
    rule combine(resource({ Members }, ListItem(_)), resource({ Members }, ListItem(_))) => error

    syntax Bool ::= Resource "contained_in" Resource [function]
    // A <= B iff exists C such that A + C = B
    rule resource(bool, ListItem(A)) contained_in resource(bool, ListItem(B)) => B orBool notBool(A)

    rule resource(nat, ListItem(A)) contained_in resource(nat, ListItem(B)) => A <=Int B

    rule resource({ _ }, A) contained_in resource({ _ }, B) => A ==K B

    rule resource(_, .List) contained_in resource(_, _) => true
    rule resource(_, ListItem(_) _) contained_in resource(_, .List) => false
    rule resource(list T, ListItem(A) Rest) contained_in resource(list S, B)
         =>
         (A in B) andBool (resource(list T, Rest) contained_in resource(list S, remove(ListItem(A), B)))

    // =================================
    // subtract:
    // =================================
    syntax Resource ::= subtract(Resource, Resource) [function]
    rule subtract(error, _) => error
    rule subtract(_, error) => error

    rule subtract(resource(R, V), resource(_, .List)) => resource(R, V)

    rule subtract(resource(R, V), resource(_, V)) => resource(R, .List)

    rule subtract(resource(nat, ListItem(A)), resource(nat, ListItem(B))) => resource(nat, ListItem(A -Int B))

    rule subtract(resource(list R, A), resource(S, ListItem(B) Rest)) => subtract(resource(list R, remove(ListItem(B), A)), resource(S, Rest))

    // =================================
    // Updaters:
    // =================================
    /* syntax Updater ::= "id" */
    /*                  | updateVar(Var) */
    /*                  | listUpdater(List) */
    /*                  | updateField(Updater, Var) */
    /* syntax QuantFunc ::= "id" */
    /*                    | toQuant(TypeQuant) */
    /* syntax Map ::= runUpdater(Updater, QuantFunc, Map) [function, functional] */

    /* rule runUpdater(id, _, M) => M */

    /* rule runUpdater(updateVar(X), F, (X |-> R T) M) => (X |-> applyQuantFunc(F, R) T) M */

    /* rule runUpdater(listUpdater(.List), _, M) => M */
    /* rule runUpdater(listUpdater(ListItem(U) Rest), F, M) => runUpdater(listUpdater(Rest), F, runUpdater(U, F, M)) */

    /* rule runUpdater(updateField(U, X), F, M) => runUpdater( */

    /* syntax TypeQuant ::= applyQuantFunc(TypeQuant, TypeQuant) [function, functional] */

    // =================================
    // Locate:
    // =================================
    context (HOLE[_]):Locator
    context (_[HOLE]):Locator
    context HOLE[_ such that _(_)]

    rule <k> N:Int => ListItem(location(loc(I), resource(nat, ListItem(N)))) ... </k>
        <storage> ... .Map => loc(I) |-> resource(nat, ListItem(N)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
        requires N >=Int 0

    rule <k> B:Bool => ListItem(location(loc(I), resource(bool, ListItem(B)))) ... </k>
        <storage> ... .Map => loc(I) |-> resource(bool, ListItem(B)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    rule <k> var X : T => ListItem(location(loc(I), resource(T, .List))) ... </k>
        <lookup> ... .Map => X |-> loc(I) ... </lookup>
        <storage> ... .Map => loc(I) |-> resource(T, .List) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    context (HOLE._):Locator
    rule (Ls:List).X => getFields(Ls, X, .List)

    syntax Locator ::= getFields(List, Var, List)
    rule getFields(.List, _, Ls) => Ls
    rule <k> getFields(ListItem(location(_, resource(_, ListItem((X |-> loc(I)) _)))) Rest, X, Ls)
             => getFields(Rest, X, Ls ListItem(location(loc(I), R))) ... </k>
        <storage> ... loc(I) |-> R ... </storage>

    syntax List ::= makeLocations(StorageLoc, BaseType, List) [function, functional]
    rule makeLocations(L, T, .List) => ListItem(location(L, resource(T, .List)))
    rule makeLocations(L, T, ListItem(V)) => ListItem(location(L, resource(T, ListItem(V))))
    rule makeLocations(L, T, ListItem(V) ListItem(W) Rest) => ListItem(location(L, resource(T, ListItem(V)))) makeLocations(L, T, ListItem(W) Rest)

    rule <k> X => makeLocations(loc(I), T, Vs) ... </k>
        <lookup> ... X |-> loc(I) ... </lookup>
        <storage> ... loc(I) |-> resource(T, Vs) ... </storage>

    rule [ Locs ] => locatorList(Locs, .List)

    syntax Locator ::= locatorList(Locators, List)
    context locatorList((HOLE:Locator, _), _)

    rule locatorList(.Locators, Ks) => Ks
    rule locatorList((ListItem(location(L, R)), Rest), Ks) => locatorList(Rest, Ks ListItem(location(L, R)))

    // Select list.
    // TODO: Need to make sure that we're expanding everywhere correctly.
    rule Ls:List[Ks:List] => selectLocations(Ls, Ks)

    syntax List ::= selectLocation(List, Resource) [function, functional]
    rule selectLocation(.List, _) => .List
    rule selectLocation(ListItem(location(L, R)) _, R) => ListItem(location(L, R))
    rule selectLocation(ListItem(location(_, R1)) Rest, R2) => selectLocation(Rest, R2)
        requires R1 =/=K R2

    syntax List ::= selectLocations(List, List) [function, functional]
    rule selectLocations(_, .List) => .List
    rule selectLocations(.List, ListItem(_) _) => ListItem(error)
    rule selectLocations(Ls, ListItem(location(_, R)) Rest) =>
            #fun(Loc:List => Loc selectLocations(removeList(Loc, Ls), Rest) )(selectLocation(Ls, R))
        requires selectLocation(Ls, R) =/=K .List // This means that we didn't find one of the values we wanted to select in the source---an error.

    syntax Locator ::= locateFilter(List, TypeQuant, Var, Locators, List)

    rule Ls:List[Q such that F(Args)] => locateFilter(Ls, Q, F, Args, .List)

    rule locateFilter(.List, empty, _, _, Ls) => #if size(Ls) ==Int 0 #then .List #else revert #fi
    rule locateFilter(.List, !, _, _, Ls) => #if size(Ls) ==Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, nonempty, _, _, Ls) => #if size(Ls) >=Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, any, _, _, Ls) => Ls

    rule locateFilter(ListItem(L) Rest, Q, F, Args, Ls)
         => execute(F, appendLoc(Args, ListItem(L))) ~> check(L) ~> locateFilter(Rest, Q, F, Args, Ls)

    syntax Stmt ::= check(Location)
                  | execute(Var, Locators)

    rule <k> Loc ~> check(L) ~> locateFilter(Ls, Q, F, Args, Ks)
             => locateFilter(Ls, Q, F, Args, Ks ListItem(L)) ... </k>
        <storage> ... Loc |-> resource(bool, ListItem(true)) ... </storage>
    rule <k> Loc ~> check(_) ~> locateFilter(Ls, Q, F, Args, Ks)
             => locateFilter(Ls, Q, F, Args, Ks) ... </k>
        <storage> ... Loc |-> resource(bool, ListItem(false)) ... </storage>
        requires Q =/=K every // If Q is every, the check **must** succeed for every element.

    rule <k> { Members } => initRecord(loc(I), Members) ... </k>
        <storage> ... .Map => loc(I) |-> resource({ membersToDefs(Members) }, ListItem(.Map)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    syntax Stmt ::= initRecord(StorageLoc, RecordMembers)
    rule <k> initRecord(loc(I), .RecordMembers) => ListItem(location(loc(I), resource(T, FieldLocs))) ... </k>
        <storage> ... loc(I) |-> resource(T, FieldLocs) ... </storage>

    context initRecord(_, _ : _ |-> HOLE , _ )
    rule <k> initRecord(Loc, (X : _ T |-> ListItem(location(InitLoc, _)), Rest)) => initRecord(Loc, Rest) ... </k>
        <storage>
            ...
            (Loc |-> resource(R, ListItem(Fields)))
            (InitLoc |-> resource(T, V))
            =>
            (Loc |-> resource(R, ListItem(Fields (X |-> loc(I)))))
            (InitLoc |-> resource(T, .List))
            (loc(I) |-> resource(T, V))
            ...
        </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    // All types are always stored as their demoted value, so we simply need to demote the type.
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(R, V)) => resource(demoteBaseType(R), V)

    // =================================
    // Flows:
    // =================================
    syntax Stmt ::= useResource(Location)

    rule <k> useResource(location(L, R)) => . ... </k>
        <storage> ... L |-> (LR => subtract(LR, R)) ... </storage>
    /* // TODO: Is this right? */
    /* rule <k> useResource(location(L, resource(_, ListItem(loc(K))))) => . ... </k> */
    /*     <storage> */
    /*         ... */
    /*         L |-> resource(_, ListItem((_ |-> K) _)) */
    /*         K |-> resource(_, _ => .List) */
    /*         ... */
    /*     </storage> */

    // TODO: Make seqstrict?
    context HOLE --> _
    context _ --> HOLE

    rule .List --> ListItem(_) => . [structural]
    rule <k> (ListItem(location(P, RP)) Rest) --> ListItem(location(K, V))
             =>
             useResource(location(P, RP)) ~> Rest --> ListItem(location(K, V)) ... </k>
        <storage> ... K |-> (RK => combine(RP, RK)) ... </storage>
        requires combine(RP, RK) =/=K error

    // Flow Filter
    /* context (HOLE => resolveStorage(HOLE)) --[ _:Selector ]-> _ */
    /* context _ --[ _:Selector ]-> (HOLE => resolveStorage(HOLE)) */

    /* rule <k> SourceLoc:StorageLoc --[ Sel ]-> Dest:StorageVal */
    /*          => */
    /*          filter(Sel, resource(R, Vs), resource(R, .List), resource(R, .List), SourceLoc, Dest) */
    /*          ... */
    /*      </k> */
    /*     <storage> ... SourceLoc |-> resource(R, Vs => .List) ... </storage> */

    // Flow Var
    /* context (HOLE => resolveStorage(HOLE)) --[ _:Var ]-> _ */
    /* context _ --[ _:Var ]-> (HOLE => resolveStorage(HOLE)) */

    /* rule <k> Loc --[ X:Var ]-> D => put(resource(R, Ws), D) ... </k> */
    /*     <lookup> ... X |-> XLoc ... </lookup> */
    /*     <storage> ... (Loc |-> (resource(R, Vs) => subtract(resource(R, Vs), resource(S, Ws)))) (XLoc |-> resource(S, Ws)) ... </storage> */
    /*     requires resource(R, Ws) contained_in resource(R, Vs) */

    /* rule <k> Loc --[ X:Var ]-> _ => revert ... </k> */
    /*     <lookup> ... X |-> XLoc ... </lookup> */
    /*     <storage> ... (Loc |-> resource(R, Vs)) (XLoc |-> resource(_, Ws)) ... </storage> */
    /*     requires notBool(resource(R, Ws) contained_in resource(R, Vs)) */

    // Flow Transformer
    /* context (HOLE => resolveStorage(HOLE)) --> _(_:Vars) --> _ */
    /* context _ --> _(_:Vars) --> (HOLE => resolveStorage(HOLE)) */

    // NOTE: It is important D be a StorageVal, so that we are sure we have allocated it, if necessary.
    /* rule <k> Loc --> _(_:Vars) --> _:StorageVal => . ... </k> */
    /*     <storage> ... Loc |-> resource(_, .List) ... </storage> */

    /* rule <k> Loc --> F(Xs) --> D => transform(F(addArg(Xs, var(I))), D) ~> Loc --> F(Xs) --> D ... </k> */
    /*     <lookup> ... .Map => var(I) |-> loc(I) ... </lookup> */
    /*     <storage> */
    /*         ... */
    /*         (Loc |-> resource(R, ListItem(A) Rest)) */
    /*         => */
    /*         (Loc |-> resource(R, Rest)) */
    /*         (loc(I) |-> resource(elemtype(R), elem(ListItem(A)))) */
    /*         ... */
    /*     </storage> */
    /*     <freshCounter> I => I +Int 1 </freshCounter> */

    /* syntax Stmt ::= transform(FunctionCallResult, StorageVal) */
    /* context transform(HOLE, _) */

    /* rule <k> transform(loc(I), Dest) => put(resource(R, V), Dest) ... </k> */
    /*     <storage> ... loc(I) |-> resource(R, V) => .Map ... </storage> */

    // =================================
    // Transformer calls:
    // =================================
    syntax Stmt ::= cleanEnv(Set)
                  | setupArg(Locator, VarDef) [strict(1)]
                  | setupArgs(Locators, VarDefs)
                  | invoke(Locators, VarDefs, Stmts)

    rule setupArgs(.Locators, .VarDefs) => . [structural]
    rule setupArgs((L, Ls), (X : T, Xs)) => setupArg(L, X : T) ~> setupArgs(Ls, Xs) [structural]

    rule <k> setupArg(Ls:List, X : _ T) => . ... </k>
        <lookup> Lookup => Lookup[X <- loc(I)] </lookup>
        <storage> ... .Map => loc(I) |-> resource(T, collectLocations(Ls)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    syntax List ::= collectLocations(List) [function, functional]
    rule collectLocations(.List) => .List
    rule collectLocations(ListItem(location(_, resource(_, Vs))) Rest) => Vs collectLocations(Rest)

    rule <k> cleanEnv(ToRemove) => . ... </k>
        <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup>

    rule <k> invoke(Args, FormalArgs, Body)
             => setupArgs(Args, FormalArgs) ~>
                cleanEnv(keys(Lookup) -Set keys(makeEnv(FormalArgs))) ~>
                Body ~>
                resetEnv(Lookup) ... </k>
        <lookup> Lookup </lookup>

    rule <k> execute(F, ActualArgs) => invoke(ActualArgs, FormalArgs, insert(RetVar, loc(I)) Body) ~> loc(I) ... </k>
        <storage> ... .Map => loc(I) |-> resource(RetType, .List) ... </storage>
        <functions> ... F |-> transformer(RetVar : _:TypeQuant RetType, FormalArgs, Body) ... </functions>
        <freshCounter> I => I +Int 1 </freshCounter>

endmodule

