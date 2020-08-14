// The syntax module containing the "core" flow language.
module PURE-FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Var ::= Id
                 | Var "." Id

    syntax Var ::= var(Int) // For generated Vars
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

    syntax FunctionCall ::= Var "[" Vars "]"
    syntax Expr ::= Bool | Var | "[" "]" | "[" Var "]"
                  | "{" RecordMembers "}"
                  | "(" Expr ")"        [bracket]

    syntax SourceVal ::= "new" Var
    syntax Source ::= Expr | SourceVal
    syntax DestinationVal ::= "consume" | "var" VarDef
    syntax Destination ::= Expr | DestinationVal
    syntax StorageVal ::= SourceVal | DestinationVal
    syntax Storage ::= Source | Destination | StorageVal
    syntax Selector ::= TypeQuant VarDef "such" "that" FunctionCall

    syntax Stmt ::= Source "--[" Selector "]->" Destination
                  | Source "--[" Selector "]->" Var "-->" Destination
                  | "pass"
                  | "try" "{" Stmt "}" "catch" "(" VarDef ")" "{" Stmt "}"
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

    // Not sure why this isn't included in the standard library, but whatever.
    syntax List ::= remove(List, KItem) [function, functional]
    rule remove(.List, _) => .List
    rule remove(ListItem(X) Rest, X) => Rest
    rule remove(ListItem(Y) Rest, X) => remove(Rest, X)
        requires X =/=K Y

    syntax Bool ::= Set "is_subset_of" Set [function, functional]
    rule .Set is_subset_of _ => true
    rule (SetItem(A) As) is_subset_of Bs => (A in Bs) andBool (As is_subset_of Bs)

    syntax Type ::= demote(Type) [function, functional]
    rule demote(Q:TypeQuant T) => Q demote(T)

    syntax BaseType ::= demote(BaseType) [function, functional]
    // TODO: Write the rest of these rules
    rule demote(bool) => bool

    syntax StorageLoc ::= loc(Int)
    syntax StorageVal ::= StorageLoc
    syntax Resource ::= resource(BaseType, List)
    syntax FlowError ::= flowError(String)
    syntax Val ::= Resource | FlowError
    syntax Storage ::= Val
    syntax KResult ::= Val | StorageVal

    // =================================
    // Sequence
    // =================================
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // =================================
    // Pass
    // =================================
    rule pass => . [structural]

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
    syntax Expr ::= resolveStorage(Storage)

    rule resolveStorage(B:Bool) => resolveStorage(resource(bool, ListItem(B)))
    rule <k> resolveStorage(resource(R, V)) => loc(I) ... </k>
        <storage> ... .Map => loc(I) |-> resource(R, V) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    rule resolveStorage(consume) => consume
    rule <k> resolveStorage(X) => Loc ... </k>
        <lookup> ... X |-> Loc ... </lookup>
    /* rule <k> resolveStorage(X . F) => Loc ... </k> */
    /*     <lookup> ... X |-> XLoc ... </lookup> */
    /*     <storage> ... XLoc |-> resource(_, (F |-> Loc) _) ... </storage> */
    rule <k> resolveStorage(var X : _:TypeQuant T) => loc(I) ... </k>
        <lookup> ... .Map => X |-> loc(I) ... </lookup>
        <storage> ... .Map => loc(I) |-> resource(T, .List) ... </storage>
        <freshCounter> I => I +Int 1 </freshCounter>
    rule resolveStorage(loc(I)) => loc(I)

    // NOTE: All types are always stored as their demoted value, so we simply need to demote the type.
    syntax Resource ::= demoteVal(Resource) [function, functional]
    rule demoteVal(resource(R, V)) => resource(demote(R), V)

    // =================================
    // Try-Catch:
    // =================================
    // Stores the variable/type to catch, the handler, the lookup table, the storage to restore to, and the continuation.
    syntax Stmt ::= catch(Var, Type, Stmt, Map, Map, K)
    /* syntax Stmt ::= "revert" "(" Var ")" */

    /* rule <k> try { S1 } catch (X : T) { S2 } ~> K => S1 ~> dropCatch </k> */
    /*     <lookup> Lookup </lookup> */
    /*     <storage> Storage </storage> */
    /*     <catchStack> .List => ListItem(catch(X, T, S2, Lookup, Storage, K)) ... </catchStack> */

    /* rule <k> revert(V:Var) ~> _ => var X : T := V in S ~> K </k> */
    /*     <lookup> _ => Lookup </lookup> */
    /*     <storage> _ => Storage </storage> */
    /*     <catchStack> ListItem(catch(X, T, S, Lookup, Storage, K)) => .List ... </catchStack> */

    // =================================
    // Flows:
    // =================================
    rule S --[ Sel ]-> D => handleFlow(Sel, resolveStorage(S), resolveStorage(D))

    syntax Stmt ::= handleFlow(Selector, Storage, Storage) [seqstrict]

    // Consume
    rule <k> handleFlow(Sel, SourceLoc, consume) => . ... </k>
        <storage> ... (SourceLoc |-> (SV => subtract(SV, select(Sel, SV)))) ... </storage>
        requires select(Sel, SV) contained_in SV

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

    syntax Stmt ::= put(Val, StorageLoc)

    /* rule put(flowError(Err), _) => revert(flowError(Err)) */
    rule <k> put(R:Resource, Loc) => . ... </k>
        <storage> ... .Map => Loc |-> R ... </storage>

    // ==================================
    // Select
    // ==================================
    syntax Resource ::= select(Selector, Resource)
    // TODO: Handle TypeQuant assertions
    rule select(_, resource(R, .List)) => resource(R, .List)
    rule select(_ X : _ such that F[Ls], resource(R, ListItem(A) Rest)) => resource(R, .List)

    // ==================================
    // Subtract
    // ==================================
    syntax Resource ::= subtract(Resource, Resource) [function, functional]
    rule subtract(resource(X, A), resource(X, A)) => resource(X, .List)

    rule subtract(resource(list R, A), resource(list R, .List)) => resource(list R, A)
    rule subtract(resource(list R, A), resource(list R, ListItem(B) Rest))
         => subtract(resource(list R, remove(A, B)), resource(list R, Rest))

    rule subtract(resource(R, A), resource(S, _)) => resource(R, A)
        requires R =/=K S

    // ==================================
    // contained_in
    // ==================================
    syntax Bool ::= Val "contained_in" Val [function, functional]
    rule resource(R, .List) contained_in resource(R, _) => true
    rule resource(R, ListItem(_) _) contained_in resource(R, .List) => false
    rule resource(R, ListItem(A) Rest) contained_in resource(R, B)
         =>
         (A in B) andBool (resource(R, Rest) contained_in resource(R, remove(B, A)))

    // ==================================
    // single
    // ==================================
    syntax Val ::= single(BaseType, KItem) [function, functional]
    rule single(R, V) => resource(R, ListItem(V))

    // ==================================
    // Convert resources: Takes a resource value and converts it to be compatible with the specified type
    // ==================================
    syntax Val ::= convert(Resource, BaseType) [function, functional]

    // ==================================
    // Combine resources: takes two collections of values and makes a single collection.
    // ==================================
    syntax Val ::= combine(Val, Val) [function, functional]

    // Error propagation
    rule combine(flowError(E), _) => flowError(E)
    rule combine(_, flowError(E)) => flowError(E)

    // Combine as `B A` instead of `A B`, because the new values should be **appended**, not prepended.
    rule combine(resource(R, A:List), resource(R, B:List)) => resource(R, B A)

    // =================================
    // Linear Lookup Value Helper
    // =================================
    syntax Expr ::= lookupVal(StorageLoc)
    rule <k> lookupVal(Loc) => V ... </k>
        <storage> ... Loc |-> V => .Map ... </storage>

    // =================================
    // Function calls:
    // =================================
    /* syntax Stmt ::= setupArgs(Vars, VarDefs, Stmt) */
    /*               | cleanEnv(Set) */
    /*               | invoke(StorageLoc, Vars, VarDefs, Stmt) */

    /* rule setupArgs(.Vars, .VarDefs, S) => S */
    /* rule setupArgs((E, Es):Vars, (Y : T, Defs2), S) => var Y : T := E in setupArgs(Es, Defs2, S) */

    /* rule <k> cleanEnv(ToRemove) => . ... </k> */
    /*     <lookup> Lookup => removeAll(Lookup, ToRemove) </lookup> */

    /* rule <k> invoke(Loc, Args, FormalArgs, Body) => setupArgs(Args, FormalArgs, cleanEnv(keys(Lookup)) insert(this, Loc) Body) ~> resetEnv(Lookup) ... </k> */
    /*     <lookup> Lookup </lookup> */

    /* // Transactions */
    /* rule <k> X.T(ActualArgs) => invoke(Loc, ActualArgs, FormalArgs, insert(RetVar, loc(I)) S) ~> lookupVal(loc(I)) ... </k> */
    /*     <lookup> ... X |-> Loc ... </lookup> */
    /*     <storage> ... (Loc |-> resource(C, _)) (.Map => loc(I) |-> resource(RetType, .List)) ... </storage> */
    /*     <functions> ... C |-> functions((T |-> transaction(RetVar : _:TypeQuant RetType, FormalArgs, S)) _) ... </functions> */
    /*     <freshCounter> I => I +Int 1 </freshCounter> */
endmodule

