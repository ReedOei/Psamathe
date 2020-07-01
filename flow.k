require "substitution.k"
require "flow-common.k"

module FLOW
    imports FLOW-SYNTAX
    imports FLOW-COMMON
    imports DOMAINS
    imports COLLECTIONS
    imports SUBSTITUTION

    // TODO: Should these really be here?
    syntax ErrorVal ::= error(String)
    syntax Val ::= Set
                 | List
                 | some(Val)
                 | "none" [token]
                 // This can be stored in the middle of a transaction, but not at the end, unless the reference is temporary.
                 | "emptySingleton" [token]
    syntax KResult ::= Val
                     | ErrorVal
                     | Vals
                     | SpecialSelect

    syntax Id ::= "NoContract" [token]

    configuration
        <common />
        <storage> .Map </storage>
        <localTypeEnv> .Map </localTypeEnv>
        <currentContract> NoContract </currentContract>
        <activations> .Set </activations>

    syntax Resource ::= resource(TypeQuant, Type, Val)
    syntax ResourceVal ::= Resource
                         | ErrorVal
                         | "bottom" [token]

    syntax K ::= split(Selector, Resource, Storage, Storage)
               | flow(ResourceVal, Storage)
               | flowError(ErrorVal, Storage)

    syntax KItem ::= TypeMod

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    // Temporary variable declaration
    rule <k> var X : T => . ... </k>
        <localTypeEnv> ... .Map => X |-> T </localTypeEnv>

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

    // Flow rules
    rule I:Int --[ everything ]-> D => flow(resource(one, nat, I), D)
    // TODO: This doesn't have to be set. How do we know what it is? Should be declared before
    rule Str:String --[ everything ]-> D => flow(resource(set, string, SetItem(Str)), D)

    rule A --[ nothing ]-> B => .

    rule <k> S --[ Sel ]-> D => split(Sel, SV, S, D) ... </k>
         <storage> ...  S |-> SV => .Map ... </storage>

    rule split(everything, resource(Q, R, V), S, D) => split(V, resource(Q, R, V), S, D)

    rule split(N:Int, resource(one, nat, V), S, D)
         =>
         flow(resource(one, nat, V -Int N), S) ~> flow(resource(one, nat, N), D)
        requires V >=Int N

    rule split(Val, resource(Q, R, SetItem(Val) Rest), S, D)
         =>
         flow(resource(Q, R, Rest), S) ~> flow(resource(Q, R, SetItem(Val)), D)

    // Combine resources: takes two collections of resources and makes a single collection.
    syntax ResourceVal ::= combineResources(TypeQuant, TypeQuant, Type, TypeMod, Val, Val) [function]

    // TODO: Is this all the cases?
    // one => one
    rule combineResources(one, one, R, MT, A, emptySingleton) => resource(one, R, A)
    rule combineResources(one, one, R, modified(SetItem(fungible) _, nat), A, B) => resource(one, R, A +Int B)
        requires B =/=K emptySingleton
    rule combineResources(one, one, R, modified(Ms, _), A, B) => error("Destination already full!")
        requires notBool(fungible in Ms) andBool B =/=K emptySingleton

    // one => option
    rule combineResources(one, option, R, MT, A, none) => resource(option, R, some(A))
    rule combineResources(one, option, R, MT, A, some(B)) => error("Destination already full!")

    // option => option
    rule combineResources(option, option, R, MT, A, none) => resource(option, R, A)
    rule combineResources(option, option, R, MT, none, some(B)) => resource(option, R, some(B))
    rule combineResources(option, option, R, MT, some(A), some(B)) => error("Destination already full!")

    // one => set
    rule combineResources(one, set, R, MT, A, B) => resource(set, R, SetItem(A) B)
    // option => set
    rule combineResources(option, set, R, MT, none, B) => resource(set, R, B)
    rule combineResources(option, set, R, MT, some(A), B) => resource(set, R, SetItem(A) B)
    // set => set
    rule combineResources(set, set, R, MT, A:Set, B:Set) => resource(set, R, A B)
    // list => set
    rule combineResources(list, set, R, MT, A:List, B:Set) => resource(set, R, List2Set(A) B)

    // one => list
    rule combineResources(one, list, R, MT, A, B) => resource(list, R, B ListItem(A))
    // option => list
    rule combineResources(option, list, R, MT, none, B) => resource(list, R, B)
    rule combineResources(option, list, R, MT, some(A), B) => resource(list, R, B ListItem(A))
    // list => list
    rule combineResources(list, list, R, MT, A:List, B:List) => resource(list, R, B A)

    // Flow resolution
    rule <k> flow(resource(Q1, R, V), S:Storage) => flow(combineResources(Q1, Q2, R, MT, V, Cur), S) ... </k>
        <storage> ...  S |-> resource(Q2, R, Cur) => .Map ... </storage>
        <types> ... R |-> MT ... </types>

    // TODO: Type checks on S to make sure it's safe to flow this type to it
    rule <k> flow(resource(Q, R, V), S:Storage) => . ... </k>
        <storage> Store => Store (S |-> resource(Q, R, V)) </storage>
        requires notBool(S in keys(Store))

    rule flow(error(E), F) => flowError(error(E), F)

    // Consume rules
    rule <k> consume S => . ... </k>
        <storage> ... S |-> resource(Q, R, V) => .Map ... </storage>
        <types> ... R |-> modified(SetItem(consumable) _, _) ... </types>

    syntax Storage ::= "freshStorage" "(" Int ")" [freshGenerator, function, functional, klabel(freshStorage)]

    rule consume V from S => S --[ V ]-> !Fresh ~> consume !Fresh

    // =================================
    // Actions:
    // =================================

    // Action sequencing
    rule .Actions => . [structural]
    rule A1:Action As:Actions => A1 ~> As [structural]

    // Externals calls:
    syntax K ::= setupArgs(Exprs, VarDefs) [function]

    rule setupArgs(.Exprs, .VarDefs) => .
    rule setupArgs((E:Storage, Es), (Y : T, Defs2)) => (E --[ everything ]-> Y) ~> setupArgs(Es, Defs2)

    syntax K ::= pack(Id)
               | packVar(QualifiedId)
    syntax Map ::= makeEnv(VarDefs) [function]

    rule makeEnv(.VarDefs) => .Map
    rule makeEnv((Y : T, Defs)) => (Y |-> T) makeEnv(Defs)

    rule <k> pack(C) => . ... </k>
        <localTypeEnv> .Map </localTypeEnv>

    rule <k> pack(C) => packVar(X) ~> pack(C) ... </k>
        <localTypeEnv> ... X |-> T => .Map ... </localTypeEnv>

    // TODO: We'll have to handle packing fields properly (i.e., don't delete them).
    rule <k> packVar(X) => . ... </k>
        <storage> ... X |-> V => .Map ... </storage>

    rule <k> packVar(X) => . ... </k>
        <storage> Env </storage>
        requires notBool(X in keys(Env))

    // TODO: Put pack back.
    /* rule <k> call C.T(ActualArgs) => setupArgs(ActualArgs, FormalArgs) ~> S ~> pack(C) ... </k> */
    rule <k> call C.T(ActualArgs) => setupArgs(ActualArgs, FormalArgs) ~> S ... </k>
        <transactions> ... C.T |-> transaction(RetType, FormalArgs, S) ... </transactions>
        <localTypeEnv> Env => Env makeEnv(FormalArgs) </localTypeEnv>
endmodule

