// The syntax module containing the "core" flow language.
module PURE-FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Var ::= Id
                 | Var "." Id
                 | var(Int) // For generated Vars
    syntax Vars ::= List{Var, ","}

    syntax Modifier ::= "fungible"
                      | "immutable"
                      | "unique"
                      | "consumable"
                      | "asset"
    syntax Modifiers ::= List{Modifier, " "}

    syntax TypeQuant ::= "!" | "any" | "nonempty" | "empty" | "every"
    syntax RecordType ::= "{" VarDefs "}"
    syntax BaseType ::= "bool"
                      | "nat"
                      | "type" Var "is" Modifiers BaseType
                      | "list" Type
                      | RecordType
                      | "(" BaseType ")" [bracket]
    syntax Type ::= TypeQuant BaseType

    syntax VarDef ::= Var ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax RecordMember ::= Var ":" Type "|->" Var
    syntax RecordMembers ::= List{RecordMember, ","}

    syntax Expr ::= Bool | Int | Var | "[" Var "]"
                  | "{" RecordMembers "}"
                  | "(" Expr ")"        [bracket]

    syntax StorageVal ::= new(Var, Modifiers, BaseType) | "consume"
    syntax Storage ::= StorageVal | "var" VarDef | Expr
    syntax Selector ::= TypeQuant "such" "that" Var "(" Vars ")"

    syntax Stmt ::= "skip"
                  | Storage "-->" Storage
                  | Storage "--[" Var "]->" Storage
                  | Storage "--[" Selector "]->" Storage
                  | Storage "-->" Var "(" Vars ")" "-->" Storage
                  | "try" "{" Stmts "}" "catch" "{" Stmts "}"
    syntax Stmts ::= List{Stmt, ""}

    syntax Decl ::= "transformer" Id "(" VarDefs ")" "->" VarDef "{" Stmts "}"
    syntax Decls ::= List{Decl, ""}

    syntax Program ::= Decls ";" Stmts
endmodule

module PURE-FLOW
    imports PURE-FLOW-SYNTAX
    imports DOMAINS
    imports COLLECTIONS

    syntax KResult

    configuration
        <k> $PGM:Program </k>
        <functions> .Map </functions>
        /* <log stream="stdout"> .List </log> */
        <freshCounter> 0 </freshCounter>
        <lookup> .Map </lookup>
        <storage> .Map </storage>
        <catchStack> .List </catchStack>

    syntax Type ::= demote(Type) [function, functional]
    rule demote(Q:TypeQuant T) => Q demote(T)

    syntax BaseType ::= demote(BaseType) [function, functional]
    // TODO: Write the rest of these rules
    rule demote(bool) => bool
    rule demote(nat) => nat
    rule demote(type _ is _ BaseT) => demote(BaseT)
    rule demote(list T) => list demote(T)
    rule demote({ Members }) => { demoteEach(Members) }

    syntax VarDefs ::= demoteEach(VarDefs) [function, functional]
    rule demoteEach(.VarDefs) => .VarDefs
    rule demoteEach(X : T, Defs) => X : demote(T), demoteEach(Defs)

    syntax StorageLoc ::= loc(Int)
    syntax StorageVal ::= StorageLoc
    syntax Resource ::= resource(BaseType, List) | "error"
    syntax Storage ::= Resource
    syntax KResult ::= StorageVal

    syntax List ::= valueOf(Resource) [function]
    rule valueOf(resource(_, V)) => V

    syntax Set ::= modifiersToSet(Modifiers) [function, functional]
    rule modifiersToSet(.Modifiers) => .Set
    rule modifiersToSet(M:Modifier Ms) => SetItem(M) modifiersToSet(Ms)

    // =================================
    // Sequence
    // =================================
    rule .Stmts => . [structural]
    rule S1:Stmt Rest:Stmts => S1 ~> Rest [structural]

    // =================================
    // Skip
    // =================================
    rule skip => . [structural]

    // =================================
    // Declarations
    // =================================
    syntax KItem ::= transformer(VarDef, VarDefs, Stmts)

    rule .Decls ; S => S [structural]

    rule <k> (transformer F(FormalArgs) -> Ret { Body }) Decls ; S => Decls ; S </k>
        <functions> ... .Map => F |-> transformer(Ret, FormalArgs, Body) ... </functions>
        [structural]

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
    // Resolve
    // =================================
    syntax StorageVal ::= resolveStorage(Storage)

    rule resolveStorage(B:Bool) => resolveStorage(resource(bool, ListItem(B)))
    rule resolveStorage(I:Int) => resolveStorage(resource(nat, ListItem(I)))
        requires I >=Int 0 // Limitation of K---there's no built-in Nat type.
    rule <k> resolveStorage([ X ]) => resolveStorage(loc(I)) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage>
            ...
            (Loc |-> resource(R, Vs))
            =>
            (Loc |-> resource(R, .List))
            (loc(I) |-> resource(list ! R, ListItem(Vs)))
            ...
        </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    rule <k> resolveStorage(resource(R, V)) => resolveStorage(loc(I)) ... </k>
        <storage> ... .Map => loc(I) |-> resource(R, V) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    rule resolveStorage(consume) => resolveStorage(consume)
    rule <k> resolveStorage(X) => resolveStorage(Loc) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
    rule <k> resolveStorage(var X : _:TypeQuant T) => resolveStorage(loc(I)) ... </k>
        <lookup> ... .Map => X |-> loc(I) ... </lookup>
        <storage> ... .Map => loc(I) |-> resource(T, .List) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    rule <k> resolveStorage(X . Y) => resolveStorage(loc(I)) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... Loc |-> resource(_, ListItem((Y |-> loc(I)) _)) ... </storage>
    rule <k> resolveStorage({ Members }) => initRecord(loc(I), Members) ~> resolveStorage(loc(I)) ... </k>
        <storage> ... .Map => loc(I) |-> resource({ membersToDefs(Members) }, ListItem(.Map)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    syntax VarDefs ::= membersToDefs(RecordMembers) [function, functional]
    rule membersToDefs(.RecordMembers) => .VarDefs
    rule membersToDefs((X : T |-> _), Rest) => (X : T), membersToDefs(Rest)

    syntax Stmt ::= initRecord(StorageLoc, RecordMembers)
    rule initRecord(_, .RecordMembers) => .
    rule <k> initRecord(Loc, (X : _ T |-> Y, Rest)) => initRecord(Loc, Rest) ... </k>
        <lookup> ... Y |-> InitLoc ... </lookup>
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

    // NOTE: All types are always stored as their demoted value, so we simply need to demote the type.
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(R, V)) => resource(demote(R), V)

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
    syntax Stmt ::= put(Resource, StorageVal)

    rule put(_, consume) => .
    rule <k> put(resource(R, Vs), Loc) => . ... </k>
        <storage> ... Loc |-> (resource(R, Ws) => combine(resource(R, Ws), resource(R, Vs))) ... </storage>
        requires combine(resource(R, Ws), resource(R, Vs)) =/=K error
    rule <k> put(resource(R, Vs), Loc) => revert ... </k>
        <storage> ... Loc |-> resource(R, Ws) ... </storage>
        requires combine(resource(R, Ws), resource(R, Vs)) ==K error

    // =================================
    // combine(R1, R2):
    // =================================
    syntax Resource ::= combine(Resource, Resource) [function, functional]

    rule combine(error, _) => error
    rule combine(_, error) => error

    rule combine(resource(bool, ListItem(A)), resource(bool, ListItem(B))) => resource(bool, ListItem(A orBool B))
    rule combine(resource(bool, .List), resource(bool, B)) => resource(bool, B)
    rule combine(resource(bool, A), resource(nat, .List)) => resource(bool, A)

    rule combine(resource(nat, ListItem(A)), resource(nat, ListItem(B))) => resource(nat, ListItem(A +Int B))
    rule combine(resource(nat, .List), resource(nat, B)) => resource(nat, B)
    rule combine(resource(nat, A), resource(nat, .List)) => resource(nat, A)

    rule combine(resource(list R, Ws), resource(list R, Vs)) => resource(list R, Ws Vs)

    rule combine(resource({ Members }, .List), resource({ Members }, .List)) => resource({ Members }, .List)
    rule combine(resource({ Members }, .List), resource({ Members }, ListItem(FieldLocs))) => resource({ Members }, ListItem(FieldLocs))
    // Can't have combine two records because that would lead to overwriting one of them.
    rule combine(resource({ Members }, ListItem(_)), resource({ Members }, ListItem(_))) => error

    rule combine(resource(type T is Ms BaseT, A), resource(type T is Ms BaseT, B)) => resource(type T is Ms BaseT, valueOf(combine(resource(BaseT, A), resource(BaseT, B))))
        requires fungible in modifiersToSet(Ms)

    rule combine(resource(type T is Ms BaseT, .List), resource(type T is Ms BaseT, B)) => resource(type T is Ms BaseT, B)
        requires notBool(fungible in modifiersToSet(Ms))
    rule combine(resource(type T is Ms BaseT, A), resource(type T is Ms BaseT, .List)) => resource(type T is Ms BaseT, A)
        requires notBool(fungible in modifiersToSet(Ms))
    rule combine(resource(type T is Ms BaseT, ListItem(_) _), resource(type T is Ms BaseT, ListItem(_) _)) => error
        requires notBool(fungible in modifiersToSet(Ms))

    syntax Bool ::= Resource "contained_in" Resource [function]
    // A <= B iff exists C such that A + C = B
    rule resource(bool, ListItem(A)) contained_in resource(bool, ListItem(B)) => B orBool notBool(A)

    rule resource(nat, ListItem(A)) contained_in resource(nat, ListItem(B)) => A <=Int B

    rule resource({ _ }, A) contained_in resource({ _ }, B) => A ==K B

    rule resource(_, .List) contained_in resource(_, _) => true
    rule resource(_, ListItem(_) _) contained_in resource(_, .List) => false
    rule resource(list T, ListItem(A) Rest) contained_in resource(list S, B)
         =>
         (A in B) andBool (resource(list T, Rest) contained_in resource(list S, remove(B, ListItem(A))))

    // =================================
    // subtract:
    // =================================
    syntax Resource ::= subtract(Resource, Resource) [function]
    rule subtract(error, _) => error
    rule subtract(_, error) => error

    rule subtract(resource(R, V), resource(_, .List)) => resource(R, V)

    rule subtract(resource(R, V), resource(_, V)) => resource(R, .List)

    rule subtract(resource(nat, ListItem(A)), resource(nat, ListItem(B))) => resource(nat, ListItem(A -Int B))
        requires A >=Int B

    // NOTE: Boolean "subtraction" is kind of weird, but this definition is compatible with how the definition of "contained_in" above.
    rule subtract(resource(bool, ListItem(_)), resource(bool, ListItem(B))) => resource(bool, ListItem(B))

    rule subtract(resource(list R, A), resource(S, ListItem(B) Rest)) => subtract(resource(list R, remove(A, ListItem(B))), resource(S, Rest))

    // =================================
    // Flows:
    // =================================
    context (HOLE => resolveStorage(HOLE)) --> _
    context _ --> (HOLE => resolveStorage(HOLE))

    rule <k> Loc --> D => put(resource(R, Vs), D) ... </k>
        <storage> ... Loc |-> resource(R, Vs) => Loc |-> resource(R, .List) ... </storage>

    context (HOLE => resolveStorage(HOLE)) --[ _:Selector ]-> _
    context _ --[ _:Selector ]-> (HOLE => resolveStorage(HOLE))

    rule <k> SourceLoc:StorageLoc --[ Sel ]-> Dest:StorageVal
             =>
             filter(Sel, resource(R, Vs), resource(R, .List), resource(R, .List), SourceLoc, Dest)
             ...
         </k>
        <storage> ... SourceLoc |-> resource(R, Vs => .List) ... </storage>

    // TODO: Implement the rest of the flow constructs
    context (HOLE => resolveStorage(HOLE)) --[ _:Var ]-> _
    context _ --[ _:Var ]-> (HOLE => resolveStorage(HOLE))

    rule <k> Loc --[ X:Var ]-> D => put(resource(R, Ws), D) ... </k>
        <lookup> ... X |-> XLoc ... </lookup>
        <storage> ... (Loc |-> (resource(R, Vs) => subtract(resource(R, Vs), resource(S, Ws)))) (XLoc |-> resource(S, Ws)) ... </storage>
        requires resource(R, Ws) contained_in resource(R, Vs)

    rule <k> Loc --[ X:Var ]-> _ => revert ... </k>
        <lookup> ... X |-> XLoc ... </lookup>
        <storage> ... (Loc |-> resource(R, Vs)) (XLoc |-> resource(_, Ws)) ... </storage>
        requires notBool(resource(R, Ws) contained_in resource(R, Vs))

    // ==================================
    // Filter
    // ==================================
    syntax BaseType ::= elemtype(BaseType) [function, functional]
    rule elemtype(list _:TypeQuant T) => T
    rule elemtype(T) => T [owise]

    syntax List ::= elem(List) [function, functional]
    rule elem(ListItem(L:List)) => L
    rule elem(L) => L [owise]

    syntax Resource ::= filter(Selector, Resource, Resource, Resource, StorageVal, StorageVal)
    syntax FunctionCallResult ::= Var "(" Vars ")" | StorageLoc
    syntax Stmt ::= check(FunctionCallResult, KItem)
    rule filter(! such that _(_), resource(_, .List), _, resource(_, DVals), _, _) => revert
        requires size(DVals) =/=Int 1
    rule filter(nonempty such that _(_), resource(_, .List), _, resource(_, DVals), _, _) => revert
        requires size(DVals) ==Int 0
    rule filter(empty such that _(_), resource(_, .List), _, resource(_, DVals), _, _) => revert
        requires size(DVals) =/=Int 0
    // There should be nothing left in the source
    rule filter(every such that _(_), resource(_, .List), resource(_, ListItem(_) _), _, _, _) => revert
    rule filter(_, resource(_, .List), SRes, DRes, Src, Dst) => put(SRes, Src) ~> put(DRes, Dst) [owise]
    rule <k> filter(Q such that F(Vs), resource(R, ListItem(A) Rest), SRes, DRes, Src, Dst)
             =>
             check(F(addArg(Vs, var(I))), elem(ListItem(A))) ~>
             filter(Q such that F(Vs), resource(R, Rest), SRes, DRes, Src, Dst)
             ...
         </k>
        <lookup> ... .Map => var(I) |-> loc(I) ... </lookup>
        <storage> ... .Map => loc(I) |-> resource(elemtype(R), elem(ListItem(A))) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
        requires Q =/=K every

    // Ugh, for some reason I can't just write (Vs, V), so this function does that...
    syntax Vars ::= addArg(Vars, Var) [function, functional]
    rule addArg(.Vars, V) => V
    rule addArg((X, Xs), V) => X, addArg(Xs, V)

    context check(HOLE, _)
    rule <k> check(Loc, V) ~> filter(Sel, ToCheck, resource(R, Vs), DRes, Src, Dst)
             => filter(Sel, ToCheck, resource(R, Vs V), DRes, Src, Dst) ... </k>
        <storage> ... Loc |-> resource(bool, ListItem(false)) ... </storage>
    rule <k> check(Loc, V) ~> filter(Sel, ToCheck, SRes, resource(R, Vs), Src, Dst)
             => filter(Sel, ToCheck, SRes, resource(R, Vs V), Src, Dst) ... </k>
        <storage> ... Loc |-> resource(bool, ListItem(true)) ... </storage>

    // =================================
    // Transformer calls:
    // =================================
    syntax Stmt ::= cleanEnv(Set)
    syntax Stmts ::= setupArgs(Vars, VarDefs, Stmts)
                  | invoke(Vars, VarDefs, Stmts)

    rule setupArgs(.Vars, .VarDefs, S) => S
    rule <k> setupArgs((E, Es):Vars, (Y : _, Defs2), S) => setupArgs(Es, Defs2, S) ... </k>
        <lookup> Lookup => Lookup[Y <- Lookup[E]] </lookup>

    rule <k> cleanEnv(ToRemove) => . ... </k>
        <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup>

    rule <k> invoke(Args, FormalArgs, Body) => setupArgs(Args, FormalArgs, cleanEnv(keys(Lookup) -Set keys(makeEnv(FormalArgs))) Body) ~> resetEnv(Lookup) ... </k>
        <lookup> Lookup </lookup>

    rule <k> F(ActualArgs) => invoke(ActualArgs, FormalArgs, insert(RetVar, loc(I)) Body) ~> loc(I) ... </k>
        <storage> ... .Map => loc(I) |-> resource(RetType, .List) ... </storage>
        <functions> ... F |-> transformer(RetVar : _:TypeQuant RetType, FormalArgs, Body) ... </functions>
        <freshCounter> I => I +Int 1 </freshCounter>

    syntax Map ::= makeEnv(VarDefs) [function, functional]
    rule makeEnv(.VarDefs) => .Map
    rule makeEnv(X : T, Rest) => (X |-> T) makeEnv(Rest)

    // =================================
    // Helpers
    // =================================
    syntax List ::= remove(List, KItem) [function, functional]
    rule remove(.List, _) => .List
    rule remove(ListItem(X) Rest, X) => Rest
    rule remove(ListItem(X) Rest, Y) => ListItem(X) remove(Rest, Y)
        requires X =/=K Y
endmodule

