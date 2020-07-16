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
    syntax Stmt ::= processDecls(Id, Decls)

    syntax TypeMod ::= modified(Set, BaseType)
    syntax KItem ::= TypeMod

    syntax KItem ::= constructor(VarDefs, Stmt)

    rule <k> contract C { Ds } Cs ; S => processDecls(C, Ds) ~> Cs ; S ... </k>
        <contracts> ... .Map => C |-> contract C { Ds } ... </contracts>
        <fields> ... .Map => C |-> .Set ... </fields>
        <constructors> ... .Map => C |-> constructor(.VarDefs, pass) ... </constructors>
        [structural]
    rule .Contracts ; S => normalize(S) [structural]

    syntax Set ::= modToSet(Modifiers) [function]
    rule modToSet(.Modifiers) => .Set
    rule modToSet(M:Modifier Ms) => SetItem(M) modToSet(Ms)

    rule processDecls(_, .Decls) => .
    rule <k> processDecls(C, (type T is Mods BaseType) Ds) => processDecls(C, Ds) ... </k>
        <types> ... .Map => C.T |-> modified(modToSet(Mods), BaseType) ... </types>
        [structural]

    rule <k> processDecls(C, (X : T) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> (Fields => Fields SetItem(X : resolveType(C, T))) ... </fields>
        [structural]
    rule <k> processDecls(C, (X : T := E) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> (Fields => Fields SetItem(X : resolveType(C, T))) ... </fields>
        <constructors> ... C |-> constructor(_, S => S (E --> X)) ... </constructors>
        [structural]

    syntax TxData ::= transaction(Type, VarDefs, Stmt)

    syntax Type ::= varDefsToProdType(VarDefs) [function]

    rule varDefsToProdType(.VarDefs) => ! unit
    rule varDefsToProdType(_ : T1) => T1
    rule varDefsToProdType((_ : T1, _ : T2)) => ! (T1 * T2)
    rule varDefsToProdType((_ : T1, Y : T2, Z : T3, Rest)) => ! (T1 * varDefsToProdType((Y : T2, Z : T3, Rest)))

    rule <k> processDecls(C, (transaction T(Args) returns RetType : S) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> (Fields => Fields SetItem(T : any (varDefsToProdType(resolveTypes(C, Args)) ~~> resolveType(C, RetType)))) ... </fields>
        <transactions> ... .Map => C.T |-> transaction(resolveType(C, RetType), resolveTypes(C, Args), resolveTypes(C, normalizeTxBody(S))) ... </transactions>
        [structural]

    syntax Stmt ::= normalizeTxBody(Stmt) [function, functional]
    rule normalizeTxBody(S) => normalize(S pack)

    // TODO: Write this function, which is intended to perform more thorough desugaring (such as generating fresh variables for non-variable storages, etc.)
    syntax Stmt ::= normalize(Stmt) [function, functional]

    // TODO: Is this right? Probably need to split up pipelines and insert identity transformers.
    // TODO: Implement something like this
    /* rule S --[ Sel1 ]-> V:Val --[ Sel2 ]-> D */
    /*      => */
    /*      (V:Val --> !Fresh) */
    /*      (S --[ Sel1 ]-> !Fresh) */
    /*      (!Fresh --[ Sel2 ]-> D) */
    /*      [strucural] */

    rule normalize(A --[ Sel ]-> B) => A --[ Sel ]-> B
    rule normalize(var X : T := E in S:Stmt) => var X : T := E in normalize(S)
    rule normalize((var X : T := E) S) => var X : T := E in normalize(S)
    rule normalize((var X : T := E)) => var X : T := E in pass
    rule normalize(pass) => pass
    rule normalize(pack) => pack
    rule normalize(unpack(F)) => unpack(F) // TODO: Need to unpack all fields before some statement, so do something like "=> unpackAll(fieldsUsedBy(S))". Will also need to keep track of what's already unpacked.
    rule normalize(return E) => return E // TODO: Need to handle this properly.
    rule normalize(revert(E)) => revert(E)
    rule normalize(F:FunctionCall) => pack F
    rule normalize(E:Expr) => E // TODO: Any other expressions we need to handle specially?
        requires (_):FunctionCall :/=K E // Ensure E is not a transaction call, or we need to apply a different rule
    rule normalize( if E { S1 } else { S2 } ) => if E { normalize(S1) } else { normalize(S2) }
    rule normalize(S1:Stmt S2:Stmt) => normalize(S1) normalize(S2)
        requires (var _ : _ := _) :/=K S1

    syntax Set ::= fields(Set) [function, functional]

    rule fields(.Set) => .Set
    rule fields(SetItem(this.X) Rest) => SetItem(this.X) fields(Rest)
    rule fields(SetItem(A) Rest) => fields(Rest)
        requires (this._) :/=K A

    syntax Set ::= vars(Stmt) [function, functional]
                 | vars(Expr) [function, functional]
                 | vars(Exprs) [function, functional]

    rule vars(A --[ Sel ]-> B) => vars(A) |Set vars(Sel) |Set vars(B)
    rule vars(var X : T := E in S:Stmt) => vars(E) |Set vars(S)
    rule vars((var X : T := E) S) => vars(E) |Set vars(S)
    rule vars(pass) => .Set
    rule vars(pack) => .Set
    rule vars(unpack(F)) => .Set
    rule vars(return E) => vars(E)
    rule vars(S1:Stmt S2:Stmt) => vars(S1) |Set vars(S2)

    rule vars(I:Int) => .Set
    rule vars(S:String) => .Set
    rule vars(B:Bool) => .Set
    rule vars(X:Id) => SetItem(X)
    rule vars(X.T) => SetItem(X.T)
    rule vars(new C(Args)) => vars(Args)
    rule vars(X[E]) => vars(X) |Set vars(E)

    rule vars(.Exprs) => .Set
    rule vars((E, Es):Exprs) => vars(E) |Set vars(Es)

    rule vars((F(Args)):FunctionCall) => vars(F) |Set vars(Args)

    rule vars(A or B) => vars(A) |Set vars(B)
    rule vars(A and B) => vars(A) |Set vars(B)
    rule vars(A + B) => vars(A) |Set vars(B)
    rule vars(A - B) => vars(A) |Set vars(B)
    rule vars(A = B) => vars(A) |Set vars(B)
    rule vars(A <= B) => vars(A) |Set vars(B)
    rule vars(A < B) => vars(A) |Set vars(B)
    rule vars(S in X) => vars(S) |Set vars(X)
    rule vars(not A) => vars(A)
    rule vars(if B { E1 } else { E2 } ) => vars(B) |Set vars(E1) |Set vars(E2)

    syntax Type ::= resolveType(Id, Type) [function]
    syntax BaseType ::= resolveType(Id, BaseType) [function]
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
    rule resolveType(_, unit) => unit
    rule resolveType(C, T:Id) => C.T
        requires T =/=K nat andBool T =/=K bool andBool T =/=K address andBool T =/=K string
    rule resolveType(_, X.T) => X.T
    rule resolveType(C, T1 * T2) => resolveType(C, T1) * resolveType(C, T2)
    rule resolveType(C, T1 ~~> T2) => resolveType(C, T1) ~~> resolveType(C, T2)
    rule resolveType(C, Q:TypeQuant T) => Q resolveType(C, T)

    // Resolve VarDef types
    rule resolveTypes(_, .VarDefs) => .VarDefs
    rule resolveTypes(C, (X : T, Defs:VarDefs)) => X : resolveType(C, T), resolveTypes(C, Defs)

    // Resolve statement types
    rule resolveTypes(C, var X : T := E in S:Stmt) => var X : resolveType(C, T) := resolveTypes(C, E) in resolveTypes(C, S)
    rule resolveTypes(C, S --[ Sel ]-> D) => resolveTypes(C, S) --[ resolveTypes(C, Sel) ]-> resolveTypes(C, D)
    rule resolveTypes(C, S1:Stmt S2:Stmt) => resolveTypes(C, S1) resolveTypes(C, S2)
    rule resolveTypes(C, return E) => return resolveTypes(C, E)
    rule resolveTypes(C, revert(E)) => revert(resolveTypes(C, E))
    rule resolveTypes(C, pass) => pass
    rule resolveTypes(C, pack) => pack
    rule resolveTypes(C, unpack(X)) => unpack(X) // TODO: Should this have a resolve types call inside of it?

    // Resolve selector types
    rule resolveTypes(_, S:SpecialSelect) => S
    rule resolveTypes(C, Q:Quant X : T:Type such that E) => Q X : resolveType(C, T) such that resolveTypes(C, E)

    // Resolve expression types
    rule resolveTypes(_, I:Int) => I
    rule resolveTypes(_, S:String) => S
    rule resolveTypes(_, B:Bool) => B
    rule resolveTypes(_, emptyval) => emptyval
    rule resolveTypes(C, \ X : T . E) => \ X : resolveType(C, T) . resolveTypes(C, E)
    rule resolveTypes(_, X:Id) => X
    rule resolveTypes(C, X:Storage.E) => resolveTypes(C, X) . resolveTypes(C, E)
    rule resolveTypes(C, X[E]) => resolveTypes(C, X) [ resolveTypes(C, E) ]
    // TODO: Finish all cases of resolveTypes

    // Not sure why this isn't included in the standard library, but whatever.
    syntax List ::= remove(List, KItem) [function]

    rule remove(.List, _) => .List
    rule remove(ListItem(X) Rest, X) => Rest
    rule remove(ListItem(Y) Rest, X) => remove(Rest, X)
        requires X =/=K Y

    syntax Type ::= demote(Type) [function, functional]
    rule demote(Q:TypeQuant T) => Q demote(T)

    syntax BaseType ::= demote(BaseType) [function, functional]
    // TODO: Write the rest of these rules
    rule demote(nat) => nat
    rule demote(bool) => bool
    rule demote(string) => string
    rule demote(address) => address
endmodule

