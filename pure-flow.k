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

    syntax StorageVal ::= StorageLoc
                        | amount(Int) // Used when only selecting part of the value from a fungible location.

    // selected(L, V) represents a pair with a "parent" location and a value in that parent location, which may itself be a location.
    // If L = V, that means that the entire value of L was selected, and it will be emptied out if flowed.
    syntax Selected ::= selected(StorageLoc, StorageVal)

    syntax Locator ::= List // So that we can use a list of Selected values as the result value of a locator.
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
    syntax Updater ::= "id"
                     | updateLoc(StorageLoc)
                     | listUpdater(List)
                     | updateField(Updater, Var)
    syntax ConsumeFunc ::= "idConsume"
                         | subtract(Resource)
                         | consumeField(Var, ConsumeFunc)
    syntax Map ::= runUpdater(Updater, ConsumeFunc, Map) [function, functional]

    rule runUpdater(id, _, M) => M

    rule runUpdater(updateLoc(L), F, (L |-> R) M) => runConsume(M, F, L, R)

    rule runUpdater(listUpdater(.List), _, M) => M
    rule runUpdater(listUpdater(ListItem(U) Rest), F, M) => runUpdater(listUpdater(Rest), F, runUpdater(U, F, M))

    rule runUpdater(updateField(U, X), F, M) => runUpdater(U, consumeField(X, F), M)

    syntax Map ::= runConsume(Map, ConsumeFunc, StorageLoc, Resource) [function, functional]
    rule runConsume(M, idConsume, L, R) => M (L |-> R)
    rule runConsume(M, subtract(R2), L, R1) => M (L |-> subtract(R1, R2))
    rule runConsume(M, consumeField(_, _), L, resource(T, .List)) => M (L |-> resource(T, .List))
    rule runConsume(M, consumeField(X, F), L, resource(T, Vs))
         => consumeEach(M (L |-> resource(T, Vs)), X, F, Vs)

    syntax Map ::= consumeEach(Map, Var, ConsumeFunc, List) [function, functional]
    rule consumeEach(M, _, _, .List) => M
    rule consumeEach(M (XLoc |-> RX), X, F, ListItem((X |-> XLoc) _) Rest)
         => consumeEach(runConsume(M, consumeField(X, F), XLoc, RX), X, F, Rest)

    // =================================
    // Locate:
    // =================================
    context (HOLE[_]):Locator
    context (_[HOLE]):Locator
    context HOLE[_ such that _(_)]

    rule <k> N:Int => ListItem(selected(loc(I), amount(N))) ... </k>
        <storage> ... .Map => loc(I) |-> resource(nat, ListItem(N)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
        requires N >=Int 0

    rule <k> B:Bool => ListItem(selected(loc(I), loc(I))) ... </k>
        <storage> ... .Map => loc(I) |-> resource(bool, ListItem(B)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    rule <k> var X : T => ListItem(selected(loc(I), loc(I))) ... </k>
        <lookup> ... .Map => X |-> loc(I) ... </lookup>
        <storage> ... .Map => loc(I) |-> resource(T, .List) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    context (HOLE._):Locator
    rule (Ls:List).X => getFields(Ls, X, .List)

    syntax Locator ::= getFields(List, Var, List)
    rule getFields(.List, _, Ls) => Ls
    rule <k> getFields(ListItem(selected(_, loc(I))) Rest, X, Ls)
             => getFields(Rest, X, Ls ListItem(selected(loc(I), XLoc))) ... </k>
        <storage> ... loc(I) |-> resource(_, ListItem((X |-> XLoc) _)) ... </storage>

    rule <k> X => ListItem(selected(loc(I), loc(I))) ... </k>
        <lookup> ... X |-> loc(I) ... </lookup>

    rule [ Locs ] => locatorList(Locs, .List)

    syntax Locator ::= locatorList(Locators, List)
    context locatorList((HOLE:Locator, _), _)

    rule locatorList(.Locators, Ks) => Ks
    rule locatorList((ListItem(selected(L, K)), Rest), Ks) => locatorList(Rest, Ks ListItem(selected(L, K)))

    // Select list.
    // TODO: Need to make sure that we're expanding everywhere correctly.
    syntax List ::= makeLocations(StorageLoc, List) [function, functional]
    rule makeLocations(_, .List) => .List
    rule makeLocations(L, ListItem(K) Rest) => ListItem(selected(L, K)) makeLocations(L, Rest)

    // TODO: Need to properly handle nat/fungible selectors
    rule <k> ListItem(selected(_, K))[Ks:List] => selectLocations(makeLocations(K, Vs), Ks) ... </k>
        <storage> ... K |-> resource(_, Vs) ... </storage>

    syntax Locator ::= selectLocation(List, StorageVal) [function, functional]
    rule selectLocation(.List, _) => .List
    rule [[ selectLocation(ListItem(selected(L, K)) _, J) => ListItem(selected(L, K)) ]]
        <storage> ... (K |-> V) (J |-> V) ... </storage>
    rule [[ selectLocation(ListItem(selected(_, K)) Rest, J) => selectLocation(Rest, J) ]]
        <storage> ... (K |-> V) (J |-> W) ... </storage>
        requires V =/=K W

    syntax List ::= selectLocations(List, List) [function, functional]
    rule selectLocations(_, .List) => .List
    // TODO: handle thie error correctly
    rule selectLocations(.List, ListItem(_) _) => ListItem(error)
    rule selectLocations(Ls, ListItem(selected(_, J)) Rest) =>
            #fun(Loc:List => Loc selectLocations(removeList(Loc, Ls), Rest) )(selectLocation(Ls, J))
        requires selectLocation(Ls, J) =/=K .List // This means that we didn't find one of the values we wanted to select in the source---an error.

    syntax Locator ::= locateFilter(List, TypeQuant, Var, Locators, List)

    rule Ls:List[Q such that F(Args)] => locateFilter(Ls, Q, F, Args, .List)

    rule locateFilter(.List, empty, _, _, Ls) => #if size(Ls) ==Int 0 #then .List #else revert #fi
    rule locateFilter(.List, !, _, _, Ls) => #if size(Ls) ==Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, nonempty, _, _, Ls) => #if size(Ls) >=Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, any, _, _, Ls) => Ls

    rule locateFilter(ListItem(L) Rest, Q, F, Args, Ls)
         => execute(F, appendLoc(Args, ListItem(L))) ~> check(L) ~> locateFilter(Rest, Q, F, Args, Ls)

    syntax Stmt ::= check(Selected)
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

    context initRecord(_, _ : _ |-> HOLE , _ )
    rule initRecord(loc(I), .RecordMembers) => ListItem(selected(loc(I), loc(I)))
    // TODO: How to not build the record unless necessary?
    rule <k> initRecord(Loc, (X : _ |-> ListItem(selected(L, K)), Rest)) => moveResource(selected(L, K)) ~> initRecord(Loc, Rest) ... </k>
        <storage>
            ...
            (Loc |-> resource(R, ListItem(Fields)))
            =>
            (Loc |-> resource(R, ListItem(Fields (X |-> K))))
            ...
        </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    // All types are always stored as their demoted value, so we simply need to demote the type.
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(R, V)) => resource(demoteBaseType(R), V)

    // =================================
    // useResource, moveResource
    // =================================
    syntax Stmt ::= useResource(Selected)

    rule <k> useResource(selected(L, amount(N))) => . ... </k>
        <storage> ... L |-> resource(_, ListItem(M => M -Int N)) ... </storage>
        requires M >=Int N
    rule <k> useResource(selected(L, amount(N))) => revert ... </k>
        <storage> ... L |-> resource(_, ListItem(M => M -Int N)) ... </storage>
        requires N >Int M
    rule <k> useResource(selected(loc(I), loc(I))) => . ... </k>
        <storage> ... loc(I) |-> resource(_, _ => .List) ... </storage>
    rule <k> useResource(selected(loc(I), loc(J))) => . ... </k>
        <storage> ... loc(I) |-> resource(_, Vs => remove(loc(J), Vs)) ... </storage>
        requires I =/=Int J andBool loc(J) in Vs
    rule <k> useResource(selected(loc(I), loc(J))) => . ... </k>
        <storage>
            ...
            loc(I) |-> resource(_, ListItem((_ |-> loc(J)) _))
            loc(J) |-> resource(_, _ => .List)
            ...
        </storage>

    syntax Stmt ::= moveResource(Selected)

    rule <k> moveResource(selected(L, amount(N))) => . ... </k>
        <storage> ... L |-> resource(_, ListItem(M => M -Int N)) ... </storage>
        requires M >=Int N
    rule <k> moveResource(selected(L, amount(N))) => revert ... </k>
        <storage> ... L |-> resource(_, ListItem(M => M -Int N)) ... </storage>
        requires N >Int M
    rule moveResource(selected(loc(I), loc(I))) => . [structural]
    rule <k> moveResource(selected(loc(I), loc(J))) => . ... </k>
        <storage> ... loc(I) |-> resource(_, Vs => remove(loc(J), Vs)) ... </storage>
        requires I =/=Int J andBool loc(J) in Vs
    rule <k> moveResource(selected(loc(I), loc(J))) => . ... </k>
        <storage>
            ...
            loc(I) |-> resource(_, ListItem((_ |-> loc(J)) _))
            loc(J) |-> resource(_, _ => .List)
            ...
        </storage>

    // =================================
    // Flows
    // =================================
    // TODO: Make seqstrict?
    context HOLE --> _
    context _ --> HOLE

    rule .List --> ListItem(_) => . [structural]
    rule <k> (ListItem(selected(L, K)) Rest) --> ListItem(selected(P, J))
             =>
             useResource(selected(L, K)) ~> Rest --> ListItem(selected(P, J)) ... </k>
        <storage> ... (K |-> RK) (J |-> (RJ => combine(RJ, RK))) ... </storage>
        requires combine(RJ, RK) =/=K error
    // TODO: Special cases like this for fungilbe are kind of annyoing, seeing as we already defined combine() above...
    rule <k> (ListItem(selected(L, amount(N))) Rest) --> ListItem(selected(P, J))
             =>
             useResource(selected(L, amount(N))) ~> Rest --> ListItem(selected(P, J)) ... </k>
         <storage> ... J |-> resource(_, ListItem(M => M +Int N)) ... </storage>
    rule <k> (ListItem(selected(L, amount(N))) Rest) --> ListItem(selected(P, J))
             =>
             useResource(selected(L, amount(N))) ~> Rest --> ListItem(selected(P, J)) ... </k>
         <storage> ... J |-> resource(_, .List => ListItem(N)) ... </storage>

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

    // TODO: Handle if there is more than one value (need to collect or something in that case)
    // TODO: Should we be using the moveResource version or not?
    /* rule <k> setupArg(ListItem(selected(L, K)), X : _) => moveResource(selected(L, K)) ... </k> */
    rule <k> setupArg(ListItem(selected(_, K)), X : _) => . ... </k>
        <lookup> Lookup => Lookup[X <- K] </lookup>

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

