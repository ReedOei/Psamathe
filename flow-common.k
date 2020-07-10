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
            <fields> .Map </fields>
            <constructors> .Map </constructors>
            <transactions> .Map </transactions>
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

    syntax TypeMod ::= modified(Set, Type)
    syntax KItem ::= TypeMod

    syntax KItem ::= constructor(VarDefs, Stmt)

    rule <k> contract C { Ds } Cs ; S => processDecls(C, Ds) ~> Cs ; S ... </k>
        <contracts> ... .Map => C |-> contract C { Ds } ... </contracts>
        <fields> ... .Map => C |-> .Set ... </fields>
        <constructors> ... .Map => C |-> constructor(.VarDefs, pass) ... </constructors>
        [structural]
    rule .Contracts ; S => S [structural]

    syntax Set ::= modToSet(Modifiers) [function]
    rule modToSet(.Modifiers) => .Set
    rule modToSet(M:Modifier Ms) => SetItem(M) modToSet(Ms)

    rule processDecls(_, .Decls) => .
    rule <k> processDecls(C, (type T is Mods BaseType) Ds) => processDecls(C, Ds) ... </k>
        <types> ... .Map => C.T |-> modified(modToSet(Mods), BaseType) ... </types>
        [structural]

    syntax Expr ::= defaultExpr(Type) [function]

    rule <k> processDecls(C, (X : T) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> (Fields => Fields SetItem(X : canonicalize(resolveType(C, T)))) ... </fields>
        [structural]
    rule <k> processDecls(C, (X : T := E) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> (Fields => Fields SetItem(X : canonicalize(resolveType(C, T)))) ... </fields>
        <constructors> ... C |-> constructor(_, S => S (E --> X)) ... </constructors>
        [structural]

    syntax TxData ::= transaction(Type, VarDefs, Stmt)

    syntax Type ::= varDefsToProdType(VarDefs) [function]

    rule varDefsToProdType(.VarDefs) => unit
    rule varDefsToProdType(X : T1) => T1
    rule varDefsToProdType((X : T1, Y : T2)) => T1 * T2
    rule varDefsToProdType((X : T1, Y : T2, Z : T3, Rest)) => T1 * varDefsToProdType((Y : T2, Z : T3, Rest))

    rule <k> processDecls(C, (transaction T(Args) returns RetType : S) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> (Fields => Fields SetItem(T : varDefsToProdType(resolveTypes(C, Args)) ~~> resolveType(C, RetType))) ... </fields>
        <transactions> ... .Map => C.T |-> transaction(resolveType(C, RetType), resolveTypes(C, Args), resolveTypes(C, S)) ... </transactions>
        [structural]

    syntax Type ::= resolveType(Id, Type) [function]
    syntax VarDefs ::= resolveTypes(Id, VarDefs) [function]
    syntax Stmt ::= resolveTypes(Id, Stmt) [function]
    syntax Flow ::= resolveTypes(Id, Flow) [function]
    syntax Storage ::= resolveTypes(Id, Storage) [function]
    syntax Selector ::= resolveTypes(Id, Selector) [function]

    // Resolve types
    // TODO: Do this better...it's very repetitive and also just assumes all types are child types of the current contract, which may not be true.
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
    rule resolveTypes(C, return E) => return resolveTypes(C, E)

    // TODO: Implement something like this
    /* rule S --[ Sel1 ]-> V:Val --[ Sel2 ]-> D */
    /*      => */
    /*      (V:Val --> !Fresh) */
    /*      (S --[ Sel1 ]-> !Fresh) */
    /*      (!Fresh --[ Sel2 ]-> D) */
    /*      [strucural] */

    // Resolve selector types
    rule resolveTypes(_, S:SpecialSelect) => S
    rule resolveTypes(C, Q:Quant X : T:Type such that E) => Q X : resolveType(C, T) such that resolveTypes(C, E)

    // Resolve expression types
    rule resolveTypes(_, I:Int) => I
    rule resolveTypes(_, S:String) => S
    rule resolveTypes(_, B:Bool) => B
    rule resolveTypes(C, \ X : T . E) => \ X : resolveType(C, T) . resolveTypes(C, E)
    rule resolveTypes(C, X:Id) => X
    rule resolveTypes(C, X:Storage.E) => resolveTypes(C, X) . resolveTypes(C, E)
    rule resolveTypes(C, X[E]) => resolveTypes(C, X) [ resolveTypes(C, E) ]
    // TODO: Finish all cases of resolveTypes

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
    // TODO: Finish the consumable rules

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

    /* rule <k> nonAsset(T:QualifiedId) => nonAsset(Base) </k> */
    /*     <types> ... T |-> modified(Ms, Base) ... </types> */
    /*     requires notBool(asset in Ms) */

    // Not sure why this isn't included in the standard library, but whatever.
    syntax List ::= remove(List, KItem) [function]

    rule remove(.List, _) => .List
    rule remove(ListItem(X) Rest, X) => Rest
    rule remove(ListItem(Y) Rest, X) => remove(Rest, X)
        requires X =/=K Y
endmodule

