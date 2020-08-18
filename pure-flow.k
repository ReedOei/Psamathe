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
                      | "type" Var "is" Modifiers BaseType
                      | "list" Type
                      | RecordType
                      | "(" BaseType ")" [bracket]
    syntax Type ::= TypeQuant BaseType

    syntax VarDef ::= Var ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax RecordMember ::= Var ":" Type "|->" Var
    syntax RecordMembers ::= List{RecordMember, ","}

    syntax Expr ::= Bool | Var | "[" "]" | "[" Var "]"
                  | "{" RecordMembers "}"
                  | "(" Expr ")"        [bracket]

    syntax StorageVal ::= new(Var, Modifiers, BaseType) | "consume"
    syntax Storage ::= StorageVal | "var" VarDef | Expr
    syntax Selector ::= TypeQuant "such" "that" Var "(" Vars ")"

    syntax Stmt ::= Storage "-->" Storage
                  | Storage "--[" Selector "]->" Storage
                  | Storage "-->" Var "(" Vars ")" "-->" Storage
                  | "skip"
                  | "try" "{" Stmts "}" "catch" "{" Stmts "}"
                  | "transformer" Var "(" VarDefs ")" "->" VarDef "{" Stmts "}"
    syntax Stmts ::= List{Stmt, ""}

    syntax Program ::= Stmts
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
    rule demote(type _ is _ BaseT) => BaseT
    rule demote(list T) => list demote(T)
    rule demote({ Members }) => { demoteEach(Members) }

    syntax VarDefs ::= demoteEach(VarDefs) [function, functional]
    rule demoteEach(.VarDefs) => .VarDefs
    rule demoteEach(X : T, Defs) => X : demote(T), demoteEach(Defs)

    syntax StorageLoc ::= loc(Int)
    syntax StorageVal ::= StorageLoc
    syntax Resource ::= resource(BaseType, List)
    syntax Storage ::= Resource
    syntax KResult ::= StorageVal

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
    // Transformer Definition
    // =================================
    syntax KItem ::= transformer(VarDef, VarDefs, Stmts)

    rule <k> transformer F(FormalArgs) -> Ret { Body } => . ... </k>
        <functions> ... .Map => F |-> transformer(Ret, FormalArgs, Body) ... </functions>
        [structural]

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

    syntax Stmt ::= drop(Var)
                  | dropLoc(StorageLoc)
    rule <k> drop(X) => . ... </k>
        <lookup> ... X |-> _ => .Map ... </lookup>

    rule <k> dropLoc(Loc) => . ... </k>
        <storage> ... Loc |-> _ => .Map ... </storage>

    // =================================
    // Variable lookup
    // =================================
    syntax StorageVal ::= resolveStorage(Storage)

    rule resolveStorage(B:Bool) => resolveStorage(resource(bool, ListItem(B)))
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
    rule <k> resolveStorage(X . Y) => loc(I) ... </k>
        <lookup> ... X |-> Loc ... </lookup>
        <storage> ... Loc |-> resource(_, ListItem((Y |-> loc(I)) _)) ... </storage>
    rule <k> resolveStorage({ Members }) => initRecord(loc(I), membersToDefs(Members)) ~> loc(I) </k>
        <storage> ... .Map => loc(I) |-> resource({ membersToDefs(Members) }, ListItem(.Map)) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>

    syntax VarDefs ::= membersToDefs(RecordMembers) [function, functional]
    rule membersToDefs(.RecordMembers) => .VarDefs
    rule membersToDefs((X : T |-> _), Rest) => (X : T), membersToDefs(Rest)

    syntax Stmt ::= initRecord(StorageLoc, VarDefs)
    rule initRecord(_, .VarDefs) => .
    rule <k> initRecord(Loc, (X : _ T, Rest)) => initRecord(Loc, Rest) </k>
        <storage>
            ...
            (Loc |-> resource(R, ListItem(Fields)))
            =>
            (Loc |-> resource(R, ListItem(Fields (X |-> loc(I)))))
            (loc(I) |-> resource(T, .List))
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

    rule <k> try { S1 } catch { S2 } ~> K => S1 ~> dropCatch </k>
        <lookup> Lookup </lookup>
        <storage> Storage </storage>
        <catchStack> .List => ListItem(catch(S2, Lookup, Storage, K)) ... </catchStack>

    rule <k> revert ~> _ => S ~> K </k>
        <lookup> _ => Lookup </lookup>
        <storage> _ => Storage </storage>
        <catchStack> ListItem(catch(S, Lookup, Storage, K)) => .List ... </catchStack>

    // =================================
    // Flows:
    // =================================
    syntax Stmt ::= split(Resource, StorageLoc, StorageLoc)
                  | put(Resource, StorageVal)

    context (HOLE => resolveStorage(HOLE)) --> _
    context _ --> (HOLE => resolveStorage(HOLE))

    rule <k> Loc --> D => put(resource(R, Vs), D) ... </k>
        <storage> ... Loc |-> resource(R, Vs) => Loc |-> resource(R, .List) ... </storage>

    context (HOLE => resolveStorage(HOLE)) --[ _ ]-> _
    context _ --[ _ ]-> (HOLE => resolveStorage(HOLE))

    rule <k> SourceLoc:StorageLoc --[ Sel ]-> Dest:StorageVal
             =>
             select(Sel, resource(R, Vs), resource(R, .List), resource(R, .List), SourceLoc, Dest)
             ...
         </k>
        <storage> ... SourceLoc |-> resource(R, Vs => .List) ... </storage>

    rule put(_, consume) => .
    rule <k> put(resource(R, Vs), Loc) => . ... </k>
        <storage> ... Loc |-> resource(R, Ws => Ws Vs) ... </storage>

    // ==================================
    // Select
    // ==================================
    syntax BaseType ::= elemtype(BaseType) [function, functional]
    rule elemtype(list _:TypeQuant T) => T
    rule elemtype(T) => T [owise]

    syntax List ::= elem(List) [function, functional]
    rule elem(ListItem(L:List)) => L
    rule elem(L) => L [owise]

    syntax Resource ::= select(Selector, Resource, Resource, Resource, StorageVal, StorageVal)
    syntax FunctionCallResult ::= Var "(" Vars ")" | StorageLoc
    syntax Stmt ::= check(FunctionCallResult, KItem)
    rule select(! such that _(_), resource(_, .List), _, resource(_, DVals), _, _) => revert
        requires size(DVals) =/=Int 1
    rule select(nonempty such that _(_), resource(_, .List), _, resource(_, DVals), _, _) => revert
        requires size(DVals) ==Int 0
    rule select(empty such that _(_), resource(_, .List), _, resource(_, DVals), _, _) => revert
        requires size(DVals) =/=Int 0
    rule select(_, resource(_, .List), SRes, DRes, Src, Dst) => put(SRes, Src) ~> put(DRes, Dst) [owise]
    // TODO: Need to do some elemtype thing probably
    rule select(every such that F(Vs), resource(R, ListItem(A) Rest), SRes, resource(R, Ws), Src, Dst)
         =>
         select(every such that F(Vs), resource(R, .List), SRes, resource(R, Ws ListItem(A) Rest), Src, Dst)
    rule <k> select(Q such that F(Vs), resource(R, ListItem(A) Rest), SRes, DRes, Src, Dst)
             =>
             check(F(addArg(Vs, var(I))), elem(ListItem(A))) ~>
             select(Q such that F(Vs), resource(R, Rest), SRes, DRes, Src, Dst)
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
    rule <k> check(Loc, V) ~> select(Sel, ToCheck, resource(R, Vs), DRes, Src, Dst)
             => select(Sel, ToCheck, resource(R, Vs V), DRes, Src, Dst) ... </k>
        <storage> ... Loc |-> resource(bool, ListItem(false)) ... </storage>
    rule <k> check(Loc, V) ~> select(Sel, ToCheck, SRes, resource(R, Vs), Src, Dst)
             => select(Sel, ToCheck, SRes, resource(R, Vs V), Src, Dst) ... </k>
        <storage> ... Loc |-> resource(bool, ListItem(true)) ... </storage>

    // =================================
    // Function calls:
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
endmodule

