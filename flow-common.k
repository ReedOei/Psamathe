require "flow-syntax.k"
require "substitution.k"

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

    rule <k> contract C { Ds } Cs ; S A => processDecls(C, Ds) ~> Cs ; S A ... </k>
        <contracts> ... .Map => C |-> contract C { Ds } ... </contracts>
    rule .Contracts ; S A => S ~> A [structural]

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
    rule resolveTypes(C, S1:Stmt S2:Stmt) => resolveTypes(C, S1) resolveTypes(C, S2)

    rule S --[ Sel1 ]-> V:Val --[ Sel2 ]-> D
         =>
         (V:Val --> !Fresh)
         (S --[ Sel1 ]-> !Fresh)
         (!Fresh --[ Sel2 ]-> D)
         [strucural]

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

    syntax Type ::= canonicalize(Type) [function]

    // TODO: Finish this
    rule canonicalize(X:Id) => one X
    rule canonicalize(one Q:TypeQuant T) => canonicalize(Q T)
    rule canonicalize(Q:TypeQuant one T) => canonicalize(Q T)
    rule canonicalize(set T) => set T
    rule canonicalize(option T) => option T
    rule canonicalize(list T) => list T

    syntax K ::= checkConsumable(Type)

    rule checkConsumable(Q:TypeQuant T) => checkConsumable(T)

    rule <k> checkConsumable(T) => . ... </k>
        <types> ... T |-> modified(SetItem(consumable) _, _) ... </types>

    rule checkConsumable(T1 * T2) => checkConsumable(T1) ~> checkConsumable(T2)

    syntax K ::= nonAsset(Type)
    /* rule nonAsset(nat) => . */
    /* rule nonAsset(bool) => . */
    /* rule nonAsset(string) => . */
    /* rule nonAsset(address) => . */
    /* rule nonAsset(set T) => nonAsset(T) */
    /* rule nonAsset(list T) => nonAsset(T) */
    /* rule nonAsset(option T) => nonAsset(T) */
    /* rule nonAsset(one T) => nonAsset(T) */
    /* rule nonAsset(T1 * T2) => nonAsset(T1) ~> nonAsset(T2) */
    /* // An empty type is always fine to get rid of. */
    /* rule nonAsset(empty T) => . */

    // NOTE: The following rule intentionally commented out, because (nonempty) transformers are always resources.
    // TODO: Provide a real error message.
    // rule nonAsset(T1 ~~> T2) => .

    // TODO: Finish the consumable rules. Maybe this should be in common, because the typechecker will need this.
endmodule

