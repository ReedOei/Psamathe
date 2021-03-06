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
        <lookup> .Map </lookup>
        <storage> .Map </storage>
        <catchStack> .List </catchStack>
        <createdVals> .Map </createdVals>

    syntax StorageLoc ::= loc(Int)
    syntax Resource ::= "error"
                      | resource(BaseType, List)

    syntax StorageVal ::= StorageLoc
                        | amount(Int) // Used when only selecting part of the value from a fungible location.

    // selected(L, V) represents a pair with a "parent" location and a value in that parent location, which may itself be a location.
    // If L = V, that means that the entire value of L was selected, and it will be emptied out if flowed.
    syntax Selected ::= selected(StorageLoc, StorageVal)
                      | selectedList(BaseType, List) // List Selected
                      /* | selectedRecord(BaseType, Map) // Map Var => Selected */

    syntax Locator ::= Selected // So that we can use Selected values as the result value of a locator
    syntax KResult ::= Selected

    syntax BaseType ::= resourceType(Resource) [function, functional]
    rule resourceType(resource(T, _)) => T

    syntax List ::= valueOf(Resource) [function]
    rule valueOf(resource(_, V)) => V

    /* rule run(Stmts) => checkStmts(Stmts) ~> Stmts [structural] */
    rule run(Stmts) => checkStmts(Stmts) [structural]

    // =================================
    // Typechecking
    // =================================
    syntax KItem ::= checkDecl(Decl)

    rule <k> checkDecl(type T is _ BaseT) => modsOk(Ms) ~> typeWf(BaseT) ... </k>
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires isAsset(BaseT) impliesBool (asset in Ms)

    rule checkDecl(transformer _(FormalArgs) -> Ret : RetType { Body })
         // TODO: Determine which all arguments that are unmoved?
         => declareVars(Ret : runFunc(withQuant(empty), RetType), FormalArgs) ~>
            checkStmts(Body) ~>
            (FlowSource |- Ret : RetType ; idFunc) ~>
            clearTypeEnv(SetItem(Ret))

    syntax KItem ::= declareVars(VarDefs)
    rule declareVars(.VarDefs) => .
    rule <k> declareVars(X : T, Rest) => declareVars(Rest) ... </k>
        <typeEnv> ... .Map => X |-> T ... </typeEnv>

    syntax KItem ::= clearTypeEnv(Set)
    rule <k> clearTypeEnv(Vs) ... </k>
        <typeEnv> ... (X |-> T) => .Map ... </typeEnv>
        requires (X in Vs) orBool notBool(isAssetType(T))
    rule <k> clearTypeEnv(_) => . ... </k>
        <typeEnv> .Map </typeEnv>

    syntax KItem ::= modsOk(Set)
    rule modsOk(_) => . // TODO: Implement this

    syntax KItem ::= typeWf(BaseType)
    rule typeWf(nat) => .
    rule typeWf(bool) => .
    rule typeWf(string) => .
    rule typeWf(address) => .
    rule typeWf(record(Keys) { Fields }) => noDuplicates(Fields, .Set) ~> keysValid(Keys, keys(makeEnv(Fields)))
    rule typeWf(table(.Vars) _ T) => typeWf(T)
    rule typeWf(table(Keys1) _ record(Keys2) { Fields }) => typeWf(record(Keys2) { Fields })
        requires varsToSet(Keys1) <=Set varsToSet(Keys2)

    syntax KItem ::= keysValid(Vars, Set)
    rule keysValid(.Vars, _) => .
    rule keysValid((X:Var, Xs), Vs) => keysValid(Xs, Vs)
        requires X in Vs

    syntax KItem ::= noDuplicates(VarDefs, Set)
    rule noDuplicates(.VarDefs, _) => .
    rule noDuplicates((X : _, Rest), Vs) => noDuplicates(Rest, SetItem(X) Vs)
        requires notBool(X in Vs)

    syntax Bool ::= isAssetType(Type) [function, functional]
    rule isAssetType(Q T) => Q =/=K empty andBool isAsset(T)

    syntax Bool ::= isAsset(BaseType) [function, functional]
    rule isAsset(nat) => false
    rule isAsset(bool) => false
    rule isAsset(string) => false
    rule isAsset(address) => false
    rule isAsset(record(_) { Fields }) => anyAreAssets(Fields)
    rule isAsset(table(_) T) => isAssetType(T)

    syntax Bool ::= anyAreAssets(VarDefs) [function, functional]
    rule anyAreAssets(.VarDefs) => false
    rule anyAreAssets(_ : T, Rest) => isAssetType(T) orBool anyAreAssets(Rest)

    syntax KItem ::= checkStmts(Stmts)
                   | checkStmt(Stmt)

    rule checkStmts(.Stmts) => .
    rule checkStmts(S1:Stmt Rest) => checkStmt(S1) ~> checkStmts(Rest)

    syntax Mode ::= "FlowSource" | "FlowDestination"
    syntax KItem ::= Mode "|-" Locator ":" Type ";" TypeFunc

    rule checkStmt(S --> D)
         => FlowSource |- S : ?Q ?T ; withQuant(empty) ~>
            FlowDestination |- D : ?_ ?T ; combineQuant(?Q)

    rule <k> checkStmt(S --> new T(Args) --> D)
             => FlowSource |- S : ?Q1 ?T1 ; withQuant(empty) ~>
                checkArgs(Args, init(getConstructorArgs(BaseT))) ~>
                FlowDestination |- D : ?Q2 ?T2 ; combineQuant(?Q1) ~>
                typeCompat(T, ?T2) ... </k>
        <types> ... T |-> typeDef(_, BaseT) ... </types>
        requires elemtype(?Q1 ?T1) ==K last(getConstructorArgs(BaseT))

    syntax KItem ::= checkArgs(Locators, List)
    rule checkArgs(.Locators, .List) => .
    rule checkArgs((L:Locator, Ls), ListItem(T) Rest)
         => (FlowSource |- L : T ; idFunc) ~> // TODO: idFunc isn't right, fix
            checkArgs(Ls, Rest)

    syntax KItem ::= typeCompat(BaseType, BaseType)
    rule typeCompat(T, T) => .
    rule typeCompat(table(_) _ T, T) => .
    rule typeCompat(T, table(_) _ T) => .

    syntax Type ::= elemtype(Type) [function, functional]
    rule elemtype(_ table(_) Q T) => Q T
    rule elemtype(Q T) => Q T [owise]

    syntax TypeQuant ::= natToQuant(Int) [function, functional]
    rule natToQuant(0) => empty
    rule natToQuant(1) => one
    rule natToQuant(I) => nonempty
        requires I >Int 1

    // ************* Locator typing ***************
    // TODO: Not sure the best way to implement this subtyping rule
    /* rule M |- L : Q T ; Func => M |- L : ?R T ; Func ~> checkSubQuant(?R, Q) */

    rule FlowSource |- I:Int : Q nat ; _ => .
        requires I >=Int 0 andBool natToQuant(I) [= Q

    rule FlowSource |- demote(L) : TDem ; idFunc => FlowSource |- L : ?T ; idFunc
        requires demoteType(?T) ==K TDem
    rule FlowSource |- copy(L) : TDem ; _ => FlowSource |- L : ?T ; idFunc
        requires demoteType(?T) ==K TDem

    rule FlowSource |- _:Bool : one bool ; _ => .

    rule FlowSource |- [ T ; Ls ] : Q list T ; F
         => checkEach(FlowSource, T, Ls, F)
         requires natToQuant(sizeLocators(Ls)) [= Q

    rule M |- L [ Q such that F(Args) ] : Q T ; Func
         => (M |- L : ?R T ; join(Func)) ~>
            checkAtLeast(?R, Q) // TODO: Finish typechecking based on F

    syntax KItem ::= checkAtLeast(TypeQuant, TypeQuant)
    rule checkAtLeast(Q, R) => .
        requires R <=Q Q

    syntax KItem ::= checkSubQuant(TypeQuant, TypeQuant)
    rule checkSubQuant(Q, R) => .
        requires Q [= R

    rule <k> FlowDestination |- (var X : T) : empty T ; F => . ... </k>
        <typeEnv> ... .Map => X |-> runFunc(F, empty T) ... </typeEnv>

    rule <k> _ |- X : T ; F => . ... </k>
        <typeEnv> ... X |-> (T => runFunc(F, T)) ... </typeEnv>
        requires F ==K idFunc orBool notBool(isImmutable(T))

    syntax KItem ::= checkEach(Mode, Type, Locators, TypeFunc)
    rule checkEach(_, _, .Locators, _) => .
    rule checkEach(M, T, (L:Locator, Ls), F) => (M |- L : T ; F) ~> checkEach(M, T, Ls, F)

    syntax Bool ::= isImmutable(Type) [function, functional]
    rule [[ isImmutable(_ T) => true ]]
        <types> ... T |-> typeDef(Ms, _) ... </types>
        requires immutable in Ms
    rule isImmutable(_) => false [owise]

    syntax Int ::= sizeLocators(Locators) [function, functional]
    rule sizeLocators(.Locators) => 0
    rule sizeLocators(_:Locator, Ls) => 1 +Int sizeLocators(Ls)

    // ************* TypeFuncs **************
    syntax TypeFunc ::= withQuant(TypeQuant)
                      | combineQuant(TypeQuant)
                      | join(TypeFunc)
                      | "idFunc"
    syntax Type ::= runFunc(TypeFunc, Type) [function, functional]

    rule runFunc(idFunc, Q T) => Q T
    rule runFunc(withQuant(Q), _ T) => Q T
    rule runFunc(combineQuant(Q), R T) => (Q + R) T
    rule runFunc(join(F), Q T) => joinType(runFunc(F, Q T), Q T)

    // =======================================
    // Type Quantity Operators
    // =======================================
    syntax Bool ::= TypeQuant "<Q" TypeQuant [function, functional]
                  | TypeQuant "<=Q" TypeQuant [function, functional]
                  | TypeQuant "[" TypeQuant [function, functional]
                  | TypeQuant "[=" TypeQuant [function, functional]
    rule empty <Q Q => Q =/=K empty
    rule any <Q one => true
    rule any <Q nonempty => true
    rule any <Q every => true
    rule one <Q nonempty => true
    rule one <Q every => true
    rule nonempty <Q every => true
    rule _ <Q _ => false [owise]

    rule Q <=Q R => Q <Q R orBool Q ==K R

    rule Q [ R => (Q =/=K any andBool R ==K any) orBool (Q in (SetItem(one) SetItem(every)) andBool R ==K nonempty)
    rule Q [= R => Q [ R orBool Q ==K R

    syntax TypeQuant ::= min(TypeQuant, TypeQuant) [function, functional]
                       | max(TypeQuant, TypeQuant) [function, functional]
    rule min(Q, R) => #if Q <Q R #then Q #else R #fi
    rule max(Q, R) => #if Q <Q R #then R #else Q #fi

    syntax TypeQuant ::= TypeQuant "+" TypeQuant [function, functional, comm, assoc]
                       | TypeQuant "-" TypeQuant [function, functional]

    rule Q + empty => Q
    rule empty + R => R
    rule _ + every => every
    rule every + _ => every
    rule nonempty + R => nonempty requires empty <Q R andBool R <Q every
    rule Q + nonempty => nonempty requires empty <Q Q andBool Q <Q every
    rule one + R => nonempty requires empty <Q R andBool R <Q every
    rule Q + one => nonempty requires empty <Q Q andBool Q <Q every
    rule any + any => any

    rule Q - empty => Q
    rule empty - _ => empty
    rule _ - every => empty
    rule every - R => every requires R <Q every
    rule nonempty - R => any requires empty <Q R andBool R <Q every
    rule one - R => empty requires one <=Q R
    rule one - any => any
    rule any - R => any requires empty <Q R andBool R <Q every

    syntax TypeQuant ::= joinQuant(TypeQuant, TypeQuant) [function, functional]
    rule joinQuant(Q, Q) => Q
    rule joinQuant(one, every) => nonempty
    rule joinQuant(every, one) => nonempty
    rule joinQuant(_, _) => any [owise]

    syntax Type ::= joinType(Type, Type) [function, functional]
    rule joinType(Q T, R T) => joinQuant(Q, R) T

    // =================================
    // Sequence
    // =================================
    rule .Stmts => . [structural]
    rule S1:Stmt Rest:Stmts => S1 ~> Rest [structural]

    // =================================
    // Declarations
    // =================================
    syntax KItem ::= createdVals(List)

    rule <k> transformer F(FormalArgs) -> Ret { Body } => checkDecl(transformer F(FormalArgs) -> Ret { Body }) ... </k>
        <functions> ... .Map => F |-> transformer(Ret, FormalArgs, Body) ... </functions>
        [structural]

    rule <k> type T is Ms BaseT => checkDecl(type T is Ms BaseT) ... </k>
        <types> ... .Map => T |-> typeDef(modifiersToSet(Ms), BaseT) ... </types>
        requires notBool(unique in modifiersToSet(Ms))
        [structural]
    rule <k> type T is Ms BaseT => checkDecl(type T is Ms BaseT) ... </k>
        <types> ... .Map => T |-> typeDef(modifiersToSet(Ms), BaseT) ... </types>
        <createdVals> ... .Map => T |-> createdVals(.List) ... </createdVals>
        requires unique in modifiersToSet(Ms)
        [structural]

    // =================================
    // Environment Helpers
    // =================================
    syntax KItem ::= insert(Var, Selected)
                   | setLookup(Map)
    rule <k> insert(X, Sel) => . ... </k>
        <lookup> ... .Map => X |-> Sel ... </lookup>
    rule <k> setLookup(Lookup) => . ... </k>
        <lookup> _ => Lookup </lookup>

    syntax KItem ::= drop(Var)
                   | dropLoc(StorageLoc)
    rule <k> drop(X) => . ... </k>
        <lookup> ... X |-> _ => .Map ... </lookup>
    rule <k> dropLoc(Loc) => . ... </k>
        <storage> ... Loc |-> _ => .Map ... </storage>

    syntax KItem ::= setType(StorageLoc, BaseType)
    rule <k> setType(L, T) => . ... </k>
        <storage> ... L |-> resource(_ => T, _) ... </storage>

    // =================================
    // Try-Catch:
    // =================================
    // Stores the variable/type to catch, the handler, the lookup table, the storage to restore to, and the continuation.
    syntax KItem ::= catch(Stmts, Map, Map, K)
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

    rule [[ subtract(resource(T, A), resource(_, B)) => withType(T, subtract(resource(BaseT, A), resource(BaseT, B))) ]]
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires fungible in Ms

    rule subtract(resource(table(Keys) T, A), resource(S, ListItem(B) Rest)) => subtract(resource(table(Keys) T, remove(ListItem(B), A)), resource(S, Rest))

    // =================================
    // Locate:
    // =================================

    // Literals
    rule <k> N:Int => selected(loc(!I), amount(N)) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(nat, ListItem(N)) ... </storage>
        requires N >=Int 0

    rule <k> B:Bool => selected(loc(!I), loc(!I)) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(bool, ListItem(B)) ... </storage>

    // Variable declaration
    rule <k> var X : T => selected(loc(!I), loc(!I)) ... </k>
        <lookup> ... .Map => X |-> selected(loc(!I), loc(!I)) ... </lookup>
        <storage> ... .Map => loc(!I) |-> resource(T, .List) ... </storage>

    // copy
    /* context copy(HOLE) */
    rule copy(Sel:Selected) => resolveSelected(Sel) ~> doCopy(loc(!_)) [structural]

    syntax KItem ::= doCopy(StorageLoc)

    rule <k> resource(T, Vs) ~> doCopy(loc(I)) => deepCopy(loc(I), Vs) ... </k>
        <storage> ... .Map => loc(I) |-> resource(demoteBaseType(T), .List) ... </storage>

    syntax KItem ::= deepCopy(StorageLoc, List)

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
    /* context (HOLE._):Locator */
    rule Sel.X => resolveSelected(Sel) ~> getFields(X, .List)

    syntax Locator ::= getFields(Var, List)
    rule resource(_, .List) ~> getFields(_, Ls) => Ls
    rule resource(_, ListItem((X |-> XLoc) _)) ~> getFields(X, _) => selected(XLoc, XLoc)
    rule <k> resource(T, ListItem(loc(I)) Rest) ~> getFields(X, Ls)
             => resource(T, Rest) ~> getFields(X, Ls ListItem(selected(XLoc, XLoc))) ... </k>
        <storage> ... loc(I) |-> resource(_, ListItem((X |-> XLoc) _)) ... </storage>

    rule <k> X => Sel ... </k>
        <lookup> ... X |-> Sel:Selected ... </lookup>

    rule <k> [ _ T ; Locs ] => locatorList(T, Locs, .List) ... </k>

    syntax Locator ::= locatorList(BaseType, Locators, List)
    /* context locatorList(_, (HOLE:Locator, _), _) */

    rule locatorList(T, .Locators, Selected) => selectedList(T, Selected)
    rule locatorList(T, (Sel:Selected, Rest), Selected) => locatorList(T, Rest, Selected ListItem(Sel))

    // Select list.
    // TODO: Need to make sure that we're expanding everywhere correctly.
    syntax List ::= makeLocations(StorageLoc, List) [function, functional]
    rule makeLocations(_, .List) => .List
    // TODO: This is some pretty annoying special casing. Should ideally be able to do away with this.
    rule makeLocations(L, ListItem(loc(I)) Rest) => ListItem(selected(L, loc(I))) makeLocations(L, Rest)
    rule makeLocations(L, ListItem(_:Map)) => ListItem(selected(L, L))
    rule makeLocations(L, ListItem(_:Bool)) => ListItem(selected(L, L))
    rule makeLocations(L, ListItem(N:Int)) => ListItem(selected(L, amount(N)))

    syntax List ::= makeAllLocations(Selected) [function]
    rule [[ makeAllLocations(selected(_, K)) => makeLocations(K, Vs) ]]
        <storage> ... K |-> resource(_, Vs) ... </storage>
    rule makeAllLocations(selectedList(_, Sels)) => Sels
    /* rule makeAllLocations(selectedRecord(T, M)) => ListItem(selectedRecord(T, M)) */

    /* context (HOLE[_]):Locator */
    /* context (_[HOLE]):Locator */
    rule Ls:Selected[Ks:Selected] => selectLocations(makeAllLocations(Ls), makeAllLocations(Ks), .List)

    syntax List ::= keysOf(Resource) [function, functional]
                 | allKeys(Vars, Map) [function, functional]
                 | allKeysTable(BaseType, Vars, List) [function, functional]
    rule keysOf(resource(T, .List)) => ListItem(resource(T, .List))
    rule keysOf(resource(nat, V)) => ListItem(resource(nat, V))
    rule keysOf(resource(bool, V)) => ListItem(resource(bool, V))

    rule keysOf(resource(record(Keys) { Fields }, ListItem(M)))
         => ListItem(resource(record(Keys) { Fields }, ListItem(M)))
            allKeys(Keys, M)

    rule keysOf(resource(table(Keys) Q T, Vs))
         => ListItem(resource(table(Keys) Q T, Vs))
            allKeysTable(T, Keys, Vs)

    rule [[ keysOf(resource(T, V)) => keysOf(resource(demoteBaseType(T), V)) ]]
        <types> ... T |-> _ ... </types>

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
    rule getFieldType(A, record(Keys) { B : _ _, Rest }) => getFieldType(A, record(Keys) { Rest })
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
    rule [[ expandEach((X : _:Type, Rest), (X |-> XLoc) M) => (X |-> expand(R)) expandEach(Rest, M) ]]
        <storage> ... XLoc |-> R ... </storage>

    syntax Resource ::= lookupSelected(Selected) [function]
    rule [[ lookupSelected(selected(_, K)) => R ]]
        <storage> ... K |-> R </storage>
    rule [[ lookupSelected(selected(L, amount(N))) => resource(T, ListItem(N)) ]]
        <storage> ... L |-> resource(T, _) ... </storage>
    rule lookupSelected(selectedList(T, .List)) => resource(T, .List)
    rule lookupSelected(selectedList(T, ListItem(Sel) Rest)) => combine(lookupSelected(Sel), lookupSelected(selectedList(T, Rest)))

    syntax Resource ::= resolveSelected(Selected) [function]
    rule [[ resolveSelected(selected(L, L)) => R ]]
        <storage> ... L |-> R ... </storage>
    rule [[ resolveSelected(selected(L, K)) => resource(T, ListItem(K)) ]]
        <storage> ... L |-> resource(T, Vs) ... </storage>
        requires K in Vs
    rule [[ resolveSelected(selected(L, amount(N))) => resource(T, ListItem(N)) ]]
        <storage> ... L |-> resource(T, _) ... </storage>

    // Assumes that the resource is already expanded (i.e., only contains resources, not locations)
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(T, V)) => resource(demoteBaseType(T), demoteValList(V))

    syntax List ::= demoteValList(List) [function, functional]
    rule demoteValList(.List) => .List
    rule demoteValList(ListItem(N:Int) Rest) => ListItem(N) demoteValList(Rest)
    rule demoteValList(ListItem(B:Bool) Rest) => ListItem(B) demoteValList(Rest)
    rule demoteValList(ListItem(M:Map) Rest) => ListItem(demoteValMap(M)) demoteValList(Rest)
    rule demoteValList(ListItem(A) Rest) => ListItem(demoteVal(A)) demoteValList(Rest)

    syntax Map ::= demoteValMap(Map) [function, functional]
    rule demoteValMap(.Map) => .Map
    rule demoteValMap((X |-> V) Rest) => (X |-> demoteVal(V)) demoteValMap(Rest)

    syntax Locator ::= selectLocation(List, Resource)
    rule selectLocation(.List, _) => .List [structural]
    rule selectLocation(ListItem(Sel) Rest, R)
          => #if demoteVal(expand(R)) inList keysOf(demoteVal(expand(lookupSelected(Sel)))) #then
                ListItem(Sel)
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
    rule selectLocations(_, .List, Selected) => Selected [structural]
    rule selectLocations(.List, ListItem(_) _, _) => revert
    rule selectLocations(Ls, ListItem(Sel) Rest, Selected)
         => selectLocation(Ls, resolveSelected(Sel)) ~> selectLocations(Ls, Rest, Selected)
    rule Loc:List ~> selectLocations(Ls, Rest, Selected)
         => #if size(Loc) ==Int 0 #then
                // This means that we didn't find one of the values we wanted to select in the source---an error.
                revert
            #else
                selectLocations(removeList(Loc, Ls), Rest, Selected Loc)
            #fi

    syntax Locator ::= locateFilter(List, TypeQuant, Var, Locators, List)

    /* context HOLE[_:TypeQuant such that _(_)] */
    rule Ls:Selected[Q such that F(Args)] => locateFilter(makeAllLocations(Ls), Q, F, Args, .List)

    rule locateFilter(.List, empty, _, _, Ls) => #if size(Ls) ==Int 0 #then .List #else revert #fi
    rule locateFilter(.List, one, _, _, Ls) => #if size(Ls) ==Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, nonempty, _, _, Ls) => #if size(Ls) >=Int 1 #then Ls #else revert #fi
    rule locateFilter(.List, any, _, _, Ls) => Ls

    rule locateFilter(ListItem(L) Rest, Q, F, Args, Ls)
         => execute(F, appendLoc(Args, L)) ~> check(L) ~>
            locateFilter(Rest, Q, F, Args, Ls)

    syntax KItem ::= check(Selected)
                   | execute(Var, Locators)

    rule <k> selected(_, Loc) ~> check(L) ~> locateFilter(Ls, Q, F, Args, Ks)
             => locateFilter(Ls, Q, F, Args, Ks ListItem(L)) ... </k>
        <storage> ... (Loc |-> resource(bool, ListItem(true))) => .Map ... </storage>
    rule <k> selected(_, Loc) ~> check(_) ~> locateFilter(Ls, Q, F, Args, Ks)
             => locateFilter(Ls, Q, F, Args, Ks) ... </k>
        <storage> ... (Loc |-> resource(bool, ListItem(false))) => .Map ... </storage>
        requires Q =/=K every // If Q is every, the check **must** succeed for every element.

    // Records
    rule <k> record(Keys) { Members } => initRecord(loc(!I), Members) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(record(Keys) { membersToDefs(Members) }, ListItem(.Map)) ... </storage>
    syntax KItem ::= initRecord(StorageLoc, RecordMembers)

    /* context initRecord(_, _:VarDef |-> HOLE , _ ) */
    rule initRecord(loc(I), .RecordMembers) => selected(loc(I), loc(I))
    // TODO: How to not build the record unless necessary? Once we figure this out, can also use for the list literals
    // TODO: Related to above, need to implement a new selectedRecord Selected constructor to be used here
    // TODO: Should allow any kind of Selected to be used, not just selected(L, K)
    rule <k> initRecord(Loc, (X : _:Type |-> selected(L, K)), Rest)
             => resolveSelected(selected(L, K)) ~> subtractFrom(L) ~> allocate(loc(!I)) ~> initRecord(Loc, Rest) ... </k>
        <storage> ... (Loc |-> resource(_, ListItem(Fields => Fields (X |-> loc(!I))))) ... </storage>

    // =================================
    // Flow Value
    // =================================
    syntax KItem ::= combineWith(StorageLoc)
                  | subtractFrom(StorageLoc)
                  | asType(BaseType)
                  | allocate(StorageLoc)

    rule <k> R:Resource ~> allocate(loc(I)) => . ... </k>
        <storage> ... .Map => loc(I) |-> R ... </storage>

    rule <k> R:Resource ~> combineWith(loc(J)) => . ... </k>
        <storage> ... loc(J) |-> (RJ => combine(RJ, R)) ... </storage>
        requires combine(RJ, R) =/=K error

    rule <k> R:Resource ~> subtractFrom(loc(I)) => R ... </k>
        <storage> ... loc(I) |-> (RI => subtract(RI, R)) ... </storage>

    // It's fine if the keys don't match up, as long as all the fields do. In an actual implementation, we might need to change how things are stored, but not in the formalization.
    rule resource(T, V) ~> asType(T) => resource(T, V)
    rule resource(record(_) { Fields }, V) ~> asType(record(Keys) { Fields })
         => resource(record(Keys) { Fields }, V)
    rule <k> resource(T, V) ~> asType(table(Keys) Q T) => resource(table(Keys) Q T, ListItem(loc(!I))) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(T, V) ... </storage>
    rule <k> resource(record(_) { Fields }, V) ~> asType(table(Keys) Q record(Keys) { Fields })
             => resource(table(Keys) Q record(Keys) { Fields }, ListItem(loc(!I))) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(record(Keys) { Fields }, V) ... </storage>
    // TODO: Should allow casting table(_) Q T into a T if it contains at most one thing, otherwise revert.

    // =================================
    // Flows
    // =================================
    // TODO: Make seqstrict?
    /* context HOLE --> _ */
    /* context _ --> HOLE */

    rule <k> selected(L, K) --> selected(_, loc(J))
         => resolveSelected(selected(L, K)) ~> subtractFrom(L) ~> asType(T) ~> combineWith(loc(J)) ... </k>
        <storage> ... loc(J) |-> resource(T, _) ... </storage>

    rule selectedList(_, .List) --> _:Selected => . [structural]
    rule selectedList(T, ListItem(Sel) Rest) --> Dest:Selected
         => (Sel --> Dest) ~> (selectedList(T, Rest) --> Dest)

    // Flow Transformer
    /* context (HOLE --> _(_) --> _):Stmt */
    /* context (_ --> _(_) --> HOLE):Stmt */

    rule <k> (selected(L, L) --> F(Args) --> Dest:Selected):Stmt
             => selectedList(T, makeLocations(L, Vs)) --> F(Args) --> Dest ... </k>
        <storage> ... L |-> resource(T, Vs) ... </storage>
    rule (selected(L, K) --> F(Args) --> Dest:Selected):Stmt
         => execute(F, appendLoc(Args, selected(L, K))) ~> transform(Dest)
        requires L =/=K K

    rule (selectedList(_, .List) --> _(_) --> _:Selected):Stmt => . [structural]
    rule (selectedList(T, ListItem(Sel) Rest) --> F(Args) --> Dest:Selected):Stmt
         => (Sel --> F(Args) --> Dest) ~>
            (selectedList(T, Rest) --> F(Args) --> Dest)

    syntax KItem ::= transform(Selected)
    rule Res:Selected ~> transform(Sel) => Res --> Sel [structural]

    /* context (HOLE --> new _(_) --> _):Stmt */
    /* context _ --> new _(_) --> HOLE */

    // If the type is unique, we need to ensure that the request value has never been created before
    /* rule selectedList(_, .List) --> new _(_) --> _:Selected => . [structural] */
    /* rule selected(L,K) --> new T(Args) --> Dest:Selected */
    /*      => createNew(T, appendLoc(Args, selected(L, K))) ~> transform(Dest) */
    /* rule selectedList(T, ListItem(Sel) Rest) --> new T(Args) --> Dest:Selected */
    /*      => (Sel --> new T(Args) --> Dest) ~> */
    /*         (selectedList(T, Rest) --> new T(Args) --> Dest) */

    syntax Locator ::= createNew(Var, Locators)

    rule <k> createNew(T, Args)
             => initializer(BaseT, Args) --> selected(loc(!I), loc(!I)) ~> setType(loc(!I), T) ~>
                selected(loc(!I), loc(!I)) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(BaseT, .List) ... </storage>
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires notBool(unique in Ms)

    rule <k> createNew(T, Args)
             => initializer(BaseT, Args) --> selected(loc(!I), loc(!I)) ~>
                checkUnique(T, selected(loc(!I), loc(!I))) ~> setType(loc(!I), T) ~>
                selected(loc(!I), loc(!I)) ... </k>
        <storage> ... .Map => loc(!I) |-> resource(BaseT, .List) ... </storage>
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires unique in Ms

    syntax KItem ::= checkUnique(Var, Selected)
    rule <k> checkUnique(T, Sel) => . ... </k>
        <createdVals> ... T |-> createdVals(Vs => Vs ListItem(expand(resolveSelected(Sel)))) ... </createdVals>
        requires notBool(expand(resolveSelected(Sel)) inList Vs)
    rule <k> checkUnique(T, Sel) => revert ... </k>
        <createdVals> ... T |-> createdVals(Vs) ... </createdVals>
        requires expand(resolveSelected(Sel)) inList Vs

    syntax Locator ::= initializer(BaseType, Locators) [function, functional]
    rule initializer(nat, L:Locator) => L
    rule initializer(bool, L:Locator) => L
    rule initializer(record(Keys) { Fields }, Ls) => record(Keys) { makeRecordMembers(Fields, Ls) }
    rule initializer(table(_) T, Ls) => [ T ; Ls ]:Locator

    syntax RecordMembers ::= makeRecordMembers(VarDefs, Locators) [function, functional]
    rule makeRecordMembers(.VarDefs, .Locators) => .RecordMembers
    rule makeRecordMembers((X : Q T, Fields), (L, Ls)) => (X : Q T |-> L), makeRecordMembers(Fields, Ls)

    // =================================
    // Transformer calls:
    // =================================
    syntax KItem ::= setupArgs(VarDefs)
                   | initArgs(List, VarDefs)
                   | locateArgs(Locators, List)

    /* context locateArgs((HOLE:Locator, _), _) */
    rule locateArgs(.Locators, Ls) => Ls
    rule locateArgs((Sel:Selected, Rest), Ls) => locateArgs(Rest, Ls ListItem(Sel))

    rule <k> Ls:List ~> setupArgs(FormalArgs) => initArgs(Ls, FormalArgs) ... </k>
        <lookup> _ => .Map </lookup>

    rule initArgs(.List, .VarDefs) => . [structural]
    rule <k> initArgs(ListItem(Sel) Rest, (X : _ _, RestArgs)) => initArgs(Rest, RestArgs) ... </k>
        <lookup> ... .Map => X |-> Sel ... </lookup>

    rule <k> execute(F, Args)
             => locateArgs(Args, .List) ~> setupArgs(FormalArgs) ~>
                insert(RetVar, selected(loc(!I), loc(!I))) ~> Body ~>
                setLookup(Lookup) ~>
                ListItem(selected(loc(!I), loc(!I))) ... </k>
        <lookup> Lookup </lookup>
        <storage> ... .Map => loc(!I) |-> resource(RetType, .List) ... </storage>
        <functions> ... F |-> transformer(RetVar : _ RetType, FormalArgs, Body) ... </functions>

endmodule

