require "substitution.k"

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
                 | "\\" Id "." Expr [binder]
    syntax Vals ::= List{Val, ","}

    syntax Storage ::= Val
                     | Id
                     | Storage "[" Expr "]" [strict(2)]
                     | Storage "." Storage [left]

    syntax Expr ::= Storage
                  | "(" Expr ")"        [bracket]
                  | "{" Exprs "}" // Set literals
                  | "(" Exprs ")" // Tuples
                  | Id "(" Exprs ")" // Function call
                  > Expr "or" Expr [strict(1)]
                  | Expr "and" Expr [strict(1)]
                  > Expr "+" Expr [left, seqstrict]
                  | Expr "-" Expr [left, seqstrict]
                  > Expr "=" Expr [seqstrict]
                  | Expr "<=" Expr [seqstrict]
                  | Expr "<" Expr [seqstrict]
                  | Expr ">=" Expr [seqstrict]
                  | Expr ">" Expr [seqstrict]
                  > Selector "in" Storage [seqstrict]
                  | Selector "not" "in" Storage [seqstrict]
                  > "not" Expr [strict]
                  > "if" Expr "then" Expr "else" Expr [strict(1)]
    syntax Exprs ::= List{Expr, ","} [seqstrict]

    syntax SpecialSelect ::= "everything" [token]
                           // Not completely sure if "nothing" is useful, but it tends to be useful (at least formally) to have 'no-op's
                           | "nothing" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "exactly" "one"
                   | "!"
                   | "any"
                   | "*"
                   | "at" "least" "one"
                   | "+"
    syntax Selector ::= Expr
                      | SpecialSelect
                      | Quant Id "such" "that" Expr [binder]

    syntax Flow ::= Storage
                  | Storage "--[" Selector "]->" Flow [strict(2)]
                  | Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types
                  | "consume" Selector "from" Storage
                  | "consume" Storage

    // Add the built-in types to the Id sort so we can reference them in the rules below
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]

    // TODO: Maybe get rid of nonfungible or fungible and have be the default
    // TODO: Warn if people put consumable on non-asset types, because that's redundant.
    syntax Modifier ::= "nonfungible" [token]
                      | "fungible"    [token]
                      | "consumable"  [token]
                      | "asset"       [token]
    syntax Modifiers ::= List{Modifier, " "}

    syntax TypeQuant ::= "set" [token]
                       | "one" [token]
                       | "option" [token]
                       | "list" [token]

    syntax Type ::= Id
                  | Type "*" Type
                  | Type "~>" Type
                  | "(" Type ")" [bracket]
                  | TypeQuant Type

    syntax TypeDef ::= "type" Id "is" Modifiers Type
    syntax Decl ::= TypeDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | Stmt Stmt [right]

    syntax Contract ::= "contract" Id "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Program ::= Contracts ";" Stmt

    // Basic desugaring
    rule S --> D => S --[ everything ]-> D [macro]

    rule S := E => (consume S) (E --[ everything ]-> S) [macro]

    rule A > B => B < A [macro]
    rule A >= B => B <= A [macro]

    rule F:Selector not in S => not (F in S) [macro]
endmodule

module FLOW-COMMON
    imports FLOW-SYNTAX
    imports DOMAINS

    configuration
        <common>
            <k> $PGM:Program </k>
            <contracts> .Map </contracts>
            <types>
                nat |-> modified(SetItem(consumable) SetItem(fungible), nat)
                string |-> modified(SetItem(consumable) SetItem(nonfungible), string)
                bool |-> modified(SetItem(consumable) SetItem(nonfungible), bool)
                address |-> modified(SetItem(consumable) SetItem(nonfungible), address)
            </types>
            <log stream="stdout"> .List </log>
        </common>

    // Helper terms
    syntax K ::= processDecls(Id, Decls)

    syntax TypeName ::= Id
                      | qualified(Id, TypeName)

    syntax TypeMod ::= modified(Set, Type)

    rule <k> contract C { Ds } Cs ; S => processDecls(C, Ds) ~> Cs ; S ... </k>
        <contracts> ... .Map => C |-> contract C { Ds } ... </contracts>
    rule .Contracts ; S => S [structural]

    syntax Set ::= modToSet(Modifiers) [function]
    rule modToSet(.Modifiers) => .Set
    rule modToSet(M:Modifier Ms) => SetItem(M) modToSet(Ms)

    rule <k> processDecls(C, (type T is Mods BaseType) Ds) => processDecls(C, Ds) ... </k>
        <types> ... .Map => qualified(C, T) |-> modified(modToSet(Mods), BaseType) ... </types>
    rule processDecls(C, .Decls) => .

    syntax Bool ::= isFungible(TypeMod) [function]
                  | isFungible(Modifier) [function]
    rule isFungible(fungible)    => true
    rule isFungible(nonfungible) => false
    rule isFungible(consumable)  => false
    rule isFungible(asset)       => false

    rule isFungible(modified(.Set, _)) => false
    rule isFungible(modified(SetItem(M:Modifier) Ms, T)) => isFungible(M) orBool isFungible(modified(Ms, T))
endmodule

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

    configuration
        <common />
        <storage> .Map </storage>

    syntax Resource ::= resource(TypeQuant, TypeName, Val)
    syntax ResourceVal ::= Resource
                         | ErrorVal

    syntax K ::= split(Selector, Resource, Storage, Flow)
               | flow(ResourceVal, Flow)
               | flowError(ErrorVal, Flow)

    syntax KItem ::= TypeName
                   | TypeMod

    // Sequence statements
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

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

    rule <k> S --[ Sel ]-> D => flow(SV, S --[ Sel ]-> D) ... </k>
         <storage> ...  S |-> SV => .Map ... </storage>

    rule split(everything, resource(Q, R, V), S, D) => split(V, resource(Q, R, V), S, D)

    rule <k> split(N:Int, resource(one, R, V), S, D)
             =>
             flow(resource(one, R, V -Int N), S) ~> flow(resource(one, R, N), D) ... </k>
        <types> ... R |-> modified(SetItem(fungible) _, _) ... </types>
        requires V >=Int N

    rule split(Val, resource(Q, R, SetItem(Val) Rest), S, D)
         =>
         flow(resource(Q, R, Rest), S) ~> flow(resource(Q, R, SetItem(Val)), D)

    // Combine resources: takes two collections of resources and makes a single collection.
    syntax ResourceVal ::= combineResources(TypeQuant, TypeQuant, TypeName, TypeMod, Val, Val) [function]

    // TODO: Is this all the cases?
    // one => one
    rule combineResources(one, one, R, MT, A, emptySingleton) => resource(one, R, A)
    rule combineResources(one, one, R, modified(SetItem(fungible) _, nat), A, B) => resource(one, R, A +Int B)
        requires B =/=K emptySingleton
    rule combineResources(one, one, R, MT, A, B) => error("Destination already full!")
        requires notBool(isFungible(MT)) andBool B =/=K emptySingleton

    // one => option
    rule combineResources(one, option, R, MT, A, none) => resource(option, R, some(A))
    // TODO: Should this be fine, but only if MT is consumable? Probably.
    rule combineResources(one, option, R, MT, A, some(B)) => error("Destination already full!")

    // option => option
    rule combineResources(option, option, R, MT, A, none) => resource(option, R, A)
    rule combineResources(option, option, R, MT, none, some(B)) => resource(option, R, some(B))
    // TODO: These errors should print and the program should probably exit.
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
    rule flow(R:Resource, S --[ Sel ]-> D) => split(Sel, R, S, D)

    // Consume rules
    rule <k> consume S => . ... </k>
        <storage> ... S |-> resource(Q, R, V) => .Map ... </storage>
        <types> ... R |-> modified(SetItem(consumable) _, _) ... </types>

    syntax Storage ::= "freshStorage" "(" Int ")" [freshGenerator, function, functional, klabel(freshStorage)]

    rule consume V from S => S --[ V ]-> !Fresh ~> consume !Fresh
endmodule

