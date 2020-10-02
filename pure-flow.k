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
                   | typeDef(Set, BaseType)

    rule <k> (transformer F(FormalArgs) -> Ret { Body }) Decls ; S => Decls ; S </k>
        <functions> ... .Map => F |-> transformer(Ret, FormalArgs, Body) ... </functions>
        [structural]

    rule <k> (type T is Ms BaseT) Decls ; S => Decls ; S </k>
        <types> ... .Map => T |-> typeDef(modifiersToSet(Ms), BaseT) ... </types>
        [structural]

    rule .Decls ; S => S [structural]

    // =================================
    // Environment Helpers
    // =================================
    syntax Stmt ::= insert(Var, Selected)
                  | setLookup(Map)

    rule <k> insert(X, Sel) => . ... </k>
        <lookup> ... .Map => X |-> Sel ... </lookup>
    rule <k> setLookup(Lookup) => . ... </k>
        <lookup> _ => Lookup </lookup>

    syntax Stmt ::= drop(Var)
                  | dropLoc(StorageLoc)
    rule <k> drop(X) => . ... </k>
        <lookup> ... X |-> _ => .Map ... </lookup>

    rule <k> dropLoc(Loc) => . ... </k>
        <storage> ... Loc |-> _ => .Map ... </storage>

    syntax Stmt ::= setType(StorageLoc, BaseType)

    rule <k> setType(L, T) => . ... </k>
        <storage> ... L |-> resource(_ => T, _) ... </storage>

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
    syntax Resource ::= withType(BaseType, Resource) [function, functional]
    rule withType(_, error) => error
    rule withType(T, resource(_, V)) => resource(T, V)

    syntax Resource ::= combine(Resource, Resource) [function, functional]
    rule combine(error, _) => error
    rule combine(_, error) => error

    rule combine(resource(T, .List), resource(_, V)) => resource(T, V)
    rule combine(resource(T, V), resource(_, .List)) => resource(T, V)

    rule combine(resource(bool, ListItem(A)), resource(bool, ListItem(B))) => resource(bool, ListItem(A orBool B))
    rule combine(resource(bool, .List), resource(bool, B)) => resource(bool, B)
    rule combine(resource(bool, A), resource(bool, .List)) => resource(bool, A)

    rule combine(resource(nat, ListItem(A)), resource(nat, ListItem(B))) => resource(nat, ListItem(A +Int B))
    rule combine(resource(nat, .List), resource(nat, B)) => resource(nat, B)
    rule combine(resource(nat, A), resource(nat, .List)) => resource(nat, A)

    // TODO: Maybe allow custom combining functions?
    rule [[ combine(resource(T, A), resource(_, B)) => withType(T, combine(resource(BaseT, A), resource(BaseT, B))) ]]
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires fungible in Ms
    rule [[ combine(resource(T, ListItem(_) _), resource(_, ListItem(_) _)) => error ]]
        <types> ... T |-> typeDef(Ms, _) ... </types>
        requires notBool(fungible in Ms)

    // Can't have combine two records where both are nonempty, because that would lead to overwriting one of them.
    rule combine(resource(record(_) { Members }, ListItem(_)), resource(record(_) { Members }, ListItem(_))) => error

    rule combine(resource(table(Keys) T, Vs), resource(table(_) T, Ws)) => resource(table(Keys) T, Vs Ws)

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
    // Locate:
    // =================================

    // Literals
    rule <k> N:Int => ListItem(selected(loc(!I), amount(N))) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(nat, ListItem(N)) ... </storage>
        requires N >=Int 0

    rule <k> B:Bool => ListItem(selected(loc(!I), loc(!I))) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(bool, ListItem(B)) ... </storage>

    // Variable declaration
    rule <k> var X : T => ListItem(selected(loc(!I), loc(!I))) ... </k>
        <lookup> ... .Map => X |-> selected(loc(!I), loc(!I)) ... </lookup>
        <storage> ... .Map => loc(!I) |-> resource(T, .List) ... </storage>

    // copy
    context copy(HOLE)
    rule <k> copy(ListItem(selected(_, K))) => deepCopy(loc(!I), Vs) ~> ListItem(selected(loc(!I), loc(!I))) ... </k>
        <storage> ... (K |-> resource(T, Vs)) (.Map => loc(!I) |-> resource(demoteBaseType(T), .List)) ... </storage>
    rule <k> copy(ListItem(selected(L, amount(N)))) => ListItem(selected(loc(!I), loc(!I))) ... </k>
        <storage> ... (L |-> resource(T, _)) (.Map => loc(!I) |-> resource(demoteBaseType(T), ListItem(N))) ... </storage>

    syntax Stmt ::= deepCopy(StorageLoc, List)

    rule deepCopy(_, .List) => .
    rule <k> deepCopy(L, ListItem(loc(I)) Rest) => deepCopy(loc(!J), Ws) ~> deepCopy(L, Rest) ... </k>
        <storage>
            ...
            (L |-> resource(TL, Vs))
            (loc(I) |-> resource(T, Ws))
            =>
            (L |-> resource(TL, Vs ListItem(loc(!J))))
            (loc(I) |-> resource(T, Ws))
            (loc(!J) |-> resource(demoteBaseType(T), .List))
            ...
        </storage>

    rule deepCopy(_, ListItem(.Map)) => .
    rule <k> deepCopy(L, ListItem((X |-> XLoc) Fields)) => deepCopy(loc(!I), Vs) ~> deepCopy(L, ListItem(Fields)) ... </k>
        <storage>
            ...
            (L |-> resource(TL, ListItem(CurFields)))
            (XLoc |-> resource(T, Vs))
            =>
            (L |-> resource(TL, ListItem(CurFields (X |-> loc(!I)))))
            (XLoc |-> resource(T, Vs))
            (loc(!I) |-> resource(demoteBaseType(T), .List))
            ...
        </storage>

    rule <k> deepCopy(L, ListItem(V) Rest) => deepCopy(L, Rest) ... </k>
        <storage> ... L |-> resource(_, Vs => Vs ListItem(V)) ... </storage>
        [owise]

    // Field access
    context (HOLE._):Locator
    rule (Ls:List).X => getFields(Ls, X, .List)

    syntax Locator ::= getFields(List, Var, List)
    rule getFields(.List, _, Ls) => Ls
    rule <k> getFields(ListItem(selected(_, loc(I))) Rest, X, Ls)
             => getFields(Rest, X, Ls ListItem(selected(loc(I), XLoc))) ... </k>
        <storage> ... loc(I) |-> resource(_, ListItem((X |-> XLoc) _)) ... </storage>

    rule <k> X => ListItem(Sel) ... </k>
        <lookup> ... X |-> Sel ... </lookup>

    rule <k> [ _ ; Locs ] => locatorList(Locs, .List) ... </k>

    syntax Locator ::= locatorList(Locators, List)
    context locatorList((HOLE:Locator, _), _)

    rule locatorList(.Locators, Selected) => Selected
    rule locatorList((ListItem(selected(L, K)), Rest), Selected) => locatorList(Rest, Selected ListItem(selected(L, K)))

    // Select list.
    // TODO: Need to make sure that we're expanding everywhere correctly.
    syntax List ::= makeLocations(StorageLoc, List) [function, functional]
    rule makeLocations(_, .List) => .List
    // TODO: This is some pretty annoying special casing. Should ideally be able to do away with this.
    rule makeLocations(L, ListItem(loc(I)) Rest) => ListItem(selected(L, loc(I))) makeLocations(L, Rest)
    rule makeLocations(L, ListItem(_:Map)) => ListItem(selected(L, L))
    rule makeLocations(L, ListItem(_:Bool)) => ListItem(selected(L, L))
    rule makeLocations(L, ListItem(N:Int)) => ListItem(selected(L, amount(N)))

    syntax List ::= makeAllLocations(List) [function]
    rule makeAllLocations(.List) => .List
    rule [[ makeAllLocations(ListItem(selected(_, K)) Rest) => makeLocations(K, Vs) makeAllLocations(Rest) ]]
        <storage> ... K |-> resource(_, Vs) ... </storage>
    rule makeAllLocations(ListItem(selected(L, amount(N))) Rest) => ListItem(selected(L, amount(N))) makeAllLocations(Rest)

    context (HOLE[_]):Locator
    context (_[HOLE]):Locator
    rule Ls:List[Ks:List] => selectLocations(makeAllLocations(Ls), makeAllLocations(Ks), .List)

    syntax List ::= keysOf(Resource) [function, functional]
                 | allKeys(Vars, Map) [function, functional]
                 | allKeysTable(BaseType, Vars, List) [function, functional]
    // TODO: Need to demote here for when we eventually add asset keys
    rule keysOf(resource(T, .List)) => ListItem(resource(T, .List))
    rule keysOf(resource(nat, V)) => ListItem(resource(nat, V))
    rule keysOf(resource(bool, V)) => ListItem(resource(bool, V))

    rule keysOf(resource(record(Keys) { Fields }, ListItem(M)))
         => ListItem(resource(record(Keys) { Fields }, ListItem(M)))
            allKeys(Keys, M)

    rule keysOf(resource(table(Keys) Q T, Vs))
         => ListItem(resource(table(Keys) Q T, Vs))
            allKeysTable(T, Keys, Vs)

    rule allKeys(.Vars, _) => .List
    rule allKeys((A, Rest), (A |-> V) M) => ListItem(V) allKeys(Rest, M)

    rule allKeysTable(_, .Vars, _) => .List
    rule allKeysTable(T, (A, Rest), Vs)
         => ListItem(resource(list getFieldType(A, T), getFieldVals(A, Vs)))
            allKeysTable(T, Rest, Vs)

    syntax List ::= getFieldVals(Var, List) [function, functional]
    rule getFieldVals(_, .List) => .List
    rule getFieldVals(A, ListItem((A |-> V) _) Rest) => ListItem(V) getFieldVals(A, Rest)

    syntax Type ::= getFieldType(Var, BaseType) [function, functional]
    rule getFieldType(A, record(_) { A : T, _ }) => T
    rule getFieldType(A, record(Keys) { B : _, Rest }) => getFieldType(A, record(Keys) { Rest })
        requires A =/=K B

    // Takes a resource and resolves all references in it (e.g., fields) so that the entire value is contained in the resource
    syntax Resource ::= expand(Resource) [function]
    rule expand(error) => error
    rule expand(resource(nat, V)) => resource(nat, V)
    rule expand(resource(bool, V)) => resource(bool, V)

    rule expand(resource(record(Keys) { Fields }, .List)) => resource(record(Keys) { Fields }, .List)
    rule expand(resource(record(Keys) { Fields }, ListItem(M))) => resource(record(Keys) { Fields }, ListItem(expandEach(Fields, M)))

    rule expand(resource(table(Keys) T, Vs)) => resource(table(Keys) T, expandList(Vs))
    rule [[ expand(resource(T, Vs)) => withType(T, expand(resource(BaseT, Vs))) ]]
        <types> ... T |-> typeDef(_, BaseT) ... </types>

    // expandList(Ls) assumes that Ls is a list of locations, whereas expandSelecteds(Ls) assumes Ls is a list of Selected
    syntax List ::= expandList(List) [function]
    rule expandList(.List) => .List
    rule [[ expandList(ListItem(loc(I)) Rest) => ListItem(expand(R)) expandList(Rest) ]]
        <storage> ... loc(I) |-> R ... </storage>

    syntax List ::= expandSelecteds(List) [function]
    rule expandSelecteds(.List) => .List
    rule expandSelecteds(ListItem(Sel) Rest) => ListItem(expand(Sel)) expandSelecteds(Rest)

    syntax Map ::= expandEach(VarDefs, Map) [function]
    rule expandEach(.VarDefs, .Map) => .Map
    rule [[ expandEach((X : _, Rest), (X |-> XLoc) M) => (X |-> expand(R)) expandEach(Rest, M) ]]
        <storage> ... XLoc |-> R ... </storage>

    syntax Resource ::= resolveSelected(Selected) [function]
    rule [[ resolveSelected(selected(_, K)) => R ]]
        <storage> ... K |-> R </storage>
    rule [[ resolveSelected(selected(L, amount(N))) => resource(T, ListItem(N)) ]]
        <storage> ... L |-> resource(T, _) ... </storage>

    syntax Locator ::= selectLocation(List, Resource)
    rule selectLocation(.List, _) => .List
    rule selectLocation(ListItem(selected(loc(I), loc(J))) Rest, R)
          => #if expand(R) inList keysOf(expand(resolveSelected(selected(loc(I), loc(J))))) #then
                ListItem(selected(loc(I), loc(J)))
             #else
                selectLocation(Rest, R)
             #fi
    rule selectLocation(ListItem(selected(L, amount(N))) Rest, resource(T, ListItem(M)))
         => #if N >=Int M #then
                ListItem(selected(L, amount(M)))
            #else
                selectLocation(Rest, resource(T, ListItem(M)))
            #fi

    syntax Locator ::= selectLocations(List, List, List)
    rule selectLocations(_, .List, Selected) => Selected
    rule selectLocations(.List, ListItem(_) _, _) => revert
    rule selectLocations(Ls, ListItem(Sel) Rest, Selected)
         => selectLocation(Ls, resolveSelected(Sel)) ~> selectLocations(Ls, Rest, Selected)
    rule Loc:List ~> selectLocations(Ls, Rest, Selected)
         => #if Loc ==K .List #then
                // This means that we didn't find one of the values we wanted to select in the source---an error.
                selectLocations(Ls, Rest, Selected)
            #else
                selectLocations(removeList(Loc, Ls), Rest, Selected Loc)
            #fi

    syntax Locator ::= locateFilter(List, TypeQuant, Var, Locators, List)

    context HOLE[_ such that _(_)]
    rule Ls:List[Q such that F(Args)] => locateFilter(makeAllLocations(Ls), Q, F, Args, .List)

    rule locateFilter(.List, empty, _, _, Ls) => #if size(Ls) ==Int 0 #then .List #else revert #fi
    rule locateFilter(.List, !, _, _, Ls) => #if size(Ls) ==Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, nonempty, _, _, Ls) => #if size(Ls) >=Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, any, _, _, Ls) => Ls

    rule locateFilter(ListItem(L) Rest, Q, F, Args, Ls)
         => execute(F, appendLoc(Args, ListItem(L))) ~> check(L) ~>
            locateFilter(Rest, Q, F, Args, Ls)

    syntax Stmt ::= check(Selected)
                  | execute(Var, Locators)

    rule <k> ListItem(selected(_, Loc)) ~> check(L) ~> locateFilter(Ls, Q, F, Args, Ks)
             => locateFilter(Ls, Q, F, Args, Ks ListItem(L)) ... </k>
        <storage> ... (Loc |-> resource(bool, ListItem(true))) => .Map ... </storage>
    rule <k> ListItem(selected(_, Loc)) ~> check(_) ~> locateFilter(Ls, Q, F, Args, Ks)
             => locateFilter(Ls, Q, F, Args, Ks) ... </k>
        <storage> ... (Loc |-> resource(bool, ListItem(false))) => .Map ... </storage>
        requires Q =/=K every // If Q is every, the check **must** succeed for every element.

    // Records
    rule <k> record(Keys) { Members } => initRecord(loc(!I), Members) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(record(Keys) { membersToDefs(Members) }, ListItem(.Map)) ... </storage>
    syntax Stmt ::= initRecord(StorageLoc, RecordMembers)

    syntax Stmt ::= allocate(StorageLoc, Selected)

    rule <k> allocate(loc(I), selected(L, K)) => useResource(selected(L, K)) ... </k>
        <storage> ... (K |-> R) (.Map => loc(I) |-> R) ... </storage>
    rule <k> allocate(loc(I), selected(L, amount(N))) => useResource(selected(L, amount(N))) ... </k>
        <storage> ... (L |-> resource(T, _)) (.Map => loc(I) |-> resource(T, ListItem(N))) ... </storage>

    context initRecord(_, _ : _ |-> HOLE , _ )
    rule initRecord(loc(I), .RecordMembers) => ListItem(selected(loc(I), loc(I)))
    // TODO: How to not build the record unless necessary?
    rule <k> initRecord(Loc, (X : _ |-> ListItem(selected(L, K)), Rest))
             => allocate(loc(!I), selected(L, K)) ~> initRecord(Loc, Rest) ... </k>
        <storage> ... (Loc |-> resource(_, ListItem(Fields => Fields (X |-> loc(!I))))) ... </storage>

    // All types are always stored as their demoted value, so we simply need to demote the type.
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(R, V)) => resource(demoteBaseType(R), V)

    // =================================
    // useResource
    // =================================
    syntax Stmt ::= useResource(Selected)

    rule <k> useResource(selected(L, amount(N))) => . ... </k>
        <storage> ... L |-> resource(_, ListItem(M => M -Int N)) ... </storage>
        requires M >=Int N
    rule <k> useResource(selected(L, amount(N))) => revert ... </k>
        <storage> ... L |-> resource(_, ListItem(M => M -Int N)) ... </storage>
        requires N >Int M
    rule <k> useResource(selected(loc(I), loc(I))) => . ... </k>
        <storage> ... loc(I) |-> (R => subtract(R, R)) ... </storage>
    rule <k> useResource(selected(loc(I), loc(J))) => . ... </k>
        <storage> ... loc(I) |-> resource(_, Vs => remove(loc(J), Vs)) ... </storage>
        requires I =/=Int J andBool loc(J) in Vs
    rule <k> useResource(selected(loc(I), loc(J))) => . ... </k>
        <storage>
            ...
            loc(I) |-> resource(_, ListItem((_ |-> loc(J)) _))
            loc(J) |-> (R => subtract(R, R))
            ...
        </storage>

    // =================================
    // Flow Value
    // =================================
    syntax Stmt ::= flowVal(Selected, StorageLoc)
                  | selectVal(Selected, BaseType)
                  | combineWith(StorageLoc)
                  | selectedVal(Resource)

    rule <k> selectedVal(R) ~> combineWith(loc(J)) => . ... </k>
        <storage> ... loc(J) |-> (RJ => combine(RJ, R)) ... </storage>
        requires combine(RJ, R) =/=K error

    rule <k> selectVal(selected(L, K), T) => useResource(selected(L, K)) ~> selectedVal(resource(T, V)) ... </k>
        <storage> ... K |-> resource(T, V) ... </storage>
    rule selectVal(selected(L, amount(N)), T)
         => useResource(selected(L, amount(N))) ~> selectedVal(resource(T, ListItem(N)))
    rule <k> selectVal(selected(L, K), table(Keys) Q T)
             => useResource(selected(L, K)) ~> selectedVal(resource(table(Keys) Q T, ListItem(loc(!I)))) ... </k>
        <storage> ... (K |-> resource(T, V)) (.Map => loc(!I) |-> resource(T, V)) ... </storage>
    rule <k> selectVal(selected(L, amount(N)), table(Keys) Q T)
             => useResource(selected(L, amount(N))) ~> selectedVal(resource(table(Keys) Q T, ListItem(loc(!I)))) ... </k>
        <storage> ... (L |-> resource(T, _)) (.Map => loc(!I) |-> resource(T, ListItem(N))) ... </storage>

    rule <k> flowVal(Sel, loc(J)) => selectVal(Sel, T) ~> combineWith(loc(J)) ... </k>
        <storage> ... loc(J) |-> resource(T, _) ... </storage>

    // =================================
    // Flows
    // =================================
    // TODO: Make seqstrict?
    context HOLE --> _
    context _ --> HOLE

    rule .List --> ListItem(_) => . [structural]
    rule (ListItem(Sel) Rest) --> ListItem(selected(P, J))
         => flowVal(Sel, J) ~> Rest --> ListItem(selected(P, J))

    // Flow Transformer
    context (HOLE --> _(_) --> _):Stmt
    context (_ --> _(_) --> HOLE):Stmt

    rule (.List --> _(_) --> _:List):Stmt => . [structural]
    rule <k> (ListItem(selected(L, L)) --> F(Args) --> ListItem(selected(P, J))):Stmt
             => makeLocations(L, Vs) --> F(Args) --> ListItem(selected(P, J)) ... </k>
        <storage> ... L |-> resource(_, Vs) ... </storage>
    rule (ListItem(selected(L, K)) Rest) --> F(Args) --> Dest:List
         => execute(F, appendLoc(Args, ListItem(selected(L, K)))) ~>
            transform(Dest) ~>
            Rest --> F(Args) --> Dest
        requires L =/=K K

    syntax Stmt ::= transform(Locator)
    rule ListItem(selected(L, K)) ~> transform(Sel) => ListItem(selected(L, K)) --> Sel [structural]

    context HOLE --> new _(_) --> _
    context _ --> new _(_) --> HOLE

    // If the type is unique, we need to ensure that the request value has never been created before
    rule .List --> new _(_) --> _:List => . [structural]
    rule (ListItem(Sel) Rest) --> new T(Args) --> Dest:List
         => createNew(T, appendLoc(Args, ListItem(Sel))) ~> transform(Dest) ~>
            Rest --> new T(Args) --> Dest

    syntax Locator ::= createNew(Var, Locators)

    // TODO: Implement unique modifier
    rule <k> createNew(T, Args)
             => initializer(BaseT, Args) --> ListItem(selected(loc(!I), loc(!I))) ~> setType(loc(!I), T) ~>
                ListItem(selected(loc(!I), loc(!I))) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(BaseT, .List) ... </storage>
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires notBool(unique in Ms)

    syntax Locator ::= initializer(BaseType, Locators) [function, functional]

    rule initializer(nat, L:Locator) => L
    rule initializer(bool, L:Locator) => L
    rule initializer(record(Keys) { Fields }, Ls) => record(Keys) { makeRecordMembers(Fields, Ls) }
    rule initializer(table(_) T, Ls) => [ T ; Ls ]:Locator

    syntax RecordMembers ::= makeRecordMembers(VarDefs, Locators) [function, functional]
    rule makeRecordMembers(.VarDefs, .Locators) => .RecordMembers
    rule makeRecordMembers((X : T, Fields), (L, Ls)) => (X : T |-> L), makeRecordMembers(Fields, Ls)

    // =================================
    // Transformer calls:
    // =================================
    syntax Stmt ::= setupArgs(VarDefs)
                  | initArgs(List, VarDefs)

    rule <k> Ls:List ~> setupArgs(FormalArgs) => initArgs(Ls, FormalArgs) ... </k>
        <lookup> _ => .Map </lookup>

    rule initArgs(.List, .VarDefs) => . [structural]
    rule <k> initArgs(ListItem(Sel) Rest, (X : _ _, RestArgs)) => initArgs(Rest, RestArgs) ... </k>
        <lookup> ... .Map => X |-> Sel ... </lookup>

    rule <k> execute(F, Args)
             => locatorList(Args, .List) ~> setupArgs(FormalArgs) ~>
                insert(RetVar, selected(loc(!I), loc(!I))) ~> Body ~>
                setLookup(Lookup) ~>
                ListItem(selected(loc(!I), loc(!I))) ... </k>
        <lookup> Lookup </lookup>
        <storage> ... .Map => loc(!I) |-> resource(RetType, .List) ... </storage>
        <functions> ... F |-> transformer(RetVar : _ RetType, FormalArgs, Body) ... </functions>

endmodule

