require "substitution.k"

// The syntax module containing the "core" flow language.
module FLOW-CORE-SYNTAX
    imports DOMAINs-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
                 | "\\" Id ":" Type "." Expr [binder]
    syntax Vals ::= List{Val, ","}

    syntax QualifiedId ::= Id
                         | Storage "[" Expr "]" [strict(2)]
                         | Storage "." Storage [left, klabel(qualified)]

    syntax Storage ::= Val
                     | QualifiedId

    syntax Expr ::= Storage
                  | "(" Expr ")"        [bracket]
                  | "{" Exprs "}" // Set literals
                  | "(" Exprs ")" // Tuples
                  | Storage "(" Exprs ")" // Function call
                  > Expr "or" Expr [strict(1)]
                  | Expr "and" Expr [strict(1)]
                  > Expr "+" Expr [left, seqstrict]
                  | Expr "-" Expr [left, seqstrict]
                  > Expr "=" Expr [seqstrict]
                  | Expr "<=" Expr [seqstrict]
                  | Expr "<" Expr [seqstrict]
                  > Selector "in" Storage [seqstrict]
                  > "not" Expr [strict]
                  > "if" Expr "then" Expr "else" Expr [strict(1)]
    syntax Exprs ::= List{Expr, ","} [seqstrict]

    syntax SpecialSelect ::= "everything" [token]
                           | "nothing" [token]
                           // Not sure about this word choice, but it will pick an arbitrary element of
                           | "arbitrary" [token]
    // Quantifiers and their symbol synonyms
    syntax Quant ::= "!"
                   | "*"
                   | "+"
    syntax Selector ::= Expr
                      | SpecialSelect
                      | Quant Id ":" Type "such" "that" Expr [binder]

    syntax Flow ::= Storage
                  | Storage "--[" Selector "]->" Flow [strict(2)]
                  | "consume" Selector "from" Storage
                  | "consume" Storage

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

    syntax Type ::= QualifiedId
                  | Type "*" Type
                  | Type "~~>" Type
                  | "(" Type ")" [bracket]
                  | TypeQuant Type

    syntax VarDef ::= Id ":" Type
    syntax VarDefs ::= List{VarDef, ","}
    syntax TypeDef ::= "type" Id "is" Modifiers Type
    syntax FieldDef ::= VarDef
                      | VarDef ":=" Expr
    syntax TransactionDef ::= "transaction" Id "(" VarDefs ")" "returns" Type ":" Stmt
                            | "transaction" Id "(" VarDefs ")" ":" Stmt
    syntax Decl ::= TypeDef
                  | TransactionDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | "var" VarDef
                  | "var" VarDef ":=" Expr
                  | "var" VarDef "in" Stmt
                  | Stmt Stmt [right]

    // Add the built-in types to the Id sort so we can reference them in the rules
    syntax Id ::= "nat"        [token]
                | "bool"       [token]
                | "string"     [token]
                | "address"    [token]

    syntax Contract ::= "contract" Id "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Action ::= "emit" Id "(" Exprs ")"
                    | "error" "(" Expr ")"
                    | "call" Storage "(" Exprs ")"
    syntax Actions ::= List{Action, " "}

    syntax Program ::= Contracts ";" Actions
endmodule

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX
    imports FLOW-CORE-SYNTAX

    // All the new syntax here gets desugared at some point.
    syntax Expr ::= Expr ">=" Expr [seqstrict]
                  | Expr ">" Expr [seqstrict]
                  | Selector "not" "in" Storage [seqstrict]

    // Quantifiers "speaking names"
    syntax Quant ::= "exactly" "one"
                   | "any"
                   | "at" "least" "one"

    syntax Flow ::= Storage "-->" Flow
                  | Storage ":=" Expr // Assignment only allowed for consumable types

    // Basic desugaring
    rule S --> D => S --[ everything ]-> D [macro]

    // TODO: Handle intermediate flows that aren't variables by generating fresh storages
    rule S --[ Sel1 ]-> T --[ Sel2 ]-> D
         =>
         (S --[ Sel1 ]-> T)
         (T --[ Sel2 ]-> D)
         [macro]

    rule var X : T := E => (var X : T) (E --[ everything ]-> X) [macro]
    rule (var X : T) S => var X : T in S [macro]

    rule S := E => (consume S) (E --[ everything ]-> S) [macro]

    rule A > B => B < A [macro]
    rule A >= B => B <= A [macro]

    rule F:Selector not in S => not (F in S) [macro]

    rule exactly one => ! [macro]
    rule any => * [macro]
    rule at least one => + [macro]
endmodule

module FLOW-COMMON-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-COMMON
    imports FLOW-SYNTAX
    imports DOMAINS

    syntax KResult

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
            <transactions> .Map </transactions>
            <log stream="stdout"> .List </log>
        </common>

    // Helper terms
    syntax K ::= processDecls(Id, Decls)

    syntax TypeMod ::= modified(Set, Type)

    rule <k> contract C { Ds } Cs ; S => processDecls(C, Ds) ~> Cs ; S ... </k>
        <contracts> ... .Map => C |-> contract C { Ds } ... </contracts>
    rule .Contracts ; S => S [structural]

    syntax Set ::= modToSet(Modifiers) [function]
    rule modToSet(.Modifiers) => .Set
    rule modToSet(M:Modifier Ms) => SetItem(M) modToSet(Ms)

    rule processDecls(C, .Decls) => .
    rule <k> processDecls(C, (type T is Mods BaseType) Ds) => processDecls(C, Ds) ... </k>
        <types> ... .Map => C.T |-> modified(modToSet(Mods), BaseType) ... </types>

    syntax TxData ::= transaction(Type, VarDefs, Stmt)
                    | processTx(Id, Type, VarDefs, Stmt) [function]

    syntax Type ::= resolveType(Id, Type) [function]
    syntax VarDefs ::= resolveTypes(Id, VarDefs) [function]
    syntax Stmt ::= resolveTypes(Id, Stmt) [function]
    syntax Flow ::= resolveTypes(Id, Flow) [function]
    syntax Storage ::= resolveTypes(Id, Storage) [function]
    syntax Selector ::= resolveTypes(Id, Selector) [function]

    // Resolve types
    rule resolveType(_, nat) => nat
    rule resolveType(_, bool) => bool
    rule resolveType(_, string) => string
    rule resolveType(_, address) => address
    rule resolveType(C, T:Id) => C.T
        requires T =/=K nat andBool T =/=K bool andBool T =/=K address andBool T =/=K string
    rule resolveType(_, X.T) => X.T
    rule resolveType(C, T1 * T2) => resolveType(C, T1) * resolveType(C, T2)
    rule resolveType(C, T1 ~~> T2) => resolveType(C, T1) ~~> resolveType(C, T2)
    rule resolveType(C, Q:TypeQuant T) => Q resolveType(C, T)

    // Resolve VarDef types
    rule resolveTypes(C, .VarDefs) => .VarDefs
    rule resolveTypes(C, (X : T, Defs:VarDefs)) => X : resolveType(C, T), resolveTypes(C, Defs)

    // Resolve statement types
    rule resolveTypes(C, var X : T) => var X : resolveType(C, T)
    rule resolveTypes(C, S --[ Sel ]-> D) => resolveTypes(C, S) --[ resolveTypes(C, Sel) ]-> resolveTypes(C, D)
    rule resolveTypes(C, consume S) => consume resolveTypes(C, S)
    rule resolveTypes(C, consume Sel from S) => consume resolveTypes(C, Sel) from resolveTypes(C, S)
    rule resolveTypes(C, S1:Stmt S2:Stmt) => resolveTypes(C, S1) resolveTypes(C, S2)

    // Resolve selector types
    rule resolveTypes(_, S:SpecialSelect) => S
    rule resolveTypes(C, Q:Quant X : T:Type such that E) => Q X : resolveType(C, T) such that resolveTypes(C, E)

    // Resolve value types
    rule resolveTypes(_, I:Int) => I
    rule resolveTypes(_, S:String) => S
    rule resolveTypes(_, B:Bool) => B
    rule resolveTypes(C, \ X : T . E) => \ X : resolveType(C, T) . resolveTypes(C, E)
    rule resolveTypes(C, X:Id) => X
    rule resolveTypes(C, X:Storage.E) => resolveTypes(C, X) . resolveTypes(C, E)
    rule resolveTypes(C, X[E]) => resolveTypes(C, X) [ resolveTypes(C, E) ]

    // TODO: Finish all cases of resolveTypes

    rule <k> processDecls(C, (transaction T(Args) : S) Ds) => processDecls(C, Ds) ... </k>
        <transactions> ... .Map => C.T |-> transaction(resolveType(C, T), resolveTypes(C, Args), resolveTypes(C, S)) ... </transactions>

    syntax Bool ::= isFungible(TypeMod) [function]
                  | isFungible(Modifier) [function]
    rule isFungible(fungible)    => true
    rule isFungible(nonfungible) => false
    rule isFungible(consumable)  => false
    rule isFungible(asset)       => false

    rule isFungible(modified(.Set, _)) => false
    rule isFungible(modified(SetItem(M:Modifier) Ms, T)) => isFungible(M) orBool isFungible(modified(Ms, T))
endmodule

