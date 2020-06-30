require "substitution.k"

module FLOW-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int
                 | Bool
                 | String
                 | "\\" Id : Type "." Expr [binder]
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
                      | Quant Id : Type "such" "that" Expr [binder]

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

    syntax VarDef ::= Id ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax TypeDef ::= "type" Id "is" Modifiers Type
    syntax FieldDef ::= VarDef
                      | VarDef ":=" Expr
    syntax TransactionDef ::= "transaction" Id "(" VarDefs ")" "returns" Type ":"
    syntax Decl ::= TypeDef
    syntax Decls ::= List{Decl, " "}

    syntax Stmt ::= Flow
                  | "var" VarDef
                  | "var" VarDef ":=" Expr
                  | Stmt Stmt [right]

    syntax Contract ::= "contract" Id "{" Decls "}"
    syntax Contracts ::= List{Contract, " "}

    syntax Program ::= Contracts ";" Stmt

    // Basic desugaring
    rule S --> D => S --[ everything ]-> D [macro]

    rule var X : T := E => (var X : T) (E --[ everything ]-> X) [macro]

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
            <localenv> .Map </localenv>
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

