require "flow-syntax.k"

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
            <contracts> .Set </contracts>
            <fields> .Map </fields>
            <constructors> .Map </constructors>
            <functions> .Map </functions>
            <types> .Map </types>
            /* <log stream="stdout"> .List </log> */
            <freshCounter> 0 </freshCounter>
        </common>

    // Helper terms
    syntax Stmt ::= processDecls(Var, Decls)
                  | "execute"

    syntax TypeData ::= type(Set, BaseType)
    syntax KItem ::= types(Map)
                   | fields(Map)
                   | functions(Map)

    syntax KItem ::= constructor(VarDefs, Stmt)

    rule <k> contract C { Ds } Cs ; S => processDecls(C, Ds) ~> Cs ; S ... </k>
        <contracts> ... .Set => SetItem(C) ... </contracts>
        <fields> ... .Map => C |-> fields(.Map) ... </fields>
        <functions> ... .Map => C |-> functions(.Map) ... </functions>
        <types> ... .Map  => C |-> types(C |-> type(SetItem(consumable) SetItem(asset), C)) ... </types>
        <constructors> ... .Map => C |-> constructor(.VarDefs, pass) ... </constructors>
        [structural]
    rule .Contracts ; S => execute ~> normalize(S) [structural]

    syntax Set ::= modToSet(Modifiers) [function]
    rule modToSet(.Modifiers) => .Set
    rule modToSet(M:Modifier Ms) => SetItem(M) modToSet(Ms)

    rule processDecls(_, .Decls) => .
    rule <k> processDecls(C, (type T is Mods BaseType) Ds) => processDecls(C, Ds) ... </k>
        <types> ... C |-> types(Types => Types (T |-> type(modToSet(Mods), BaseType))) ... </types>
        [structural]

    rule <k> processDecls(C, (X : T) Ds) => processDecls(C, Ds) ... </k>
        <fields> ... C |-> fields(Fields => Fields (X |-> resolveType(C, T))) ... </fields>
        [structural]

    syntax FuncData ::= transaction(VarDef, VarDefs, Stmt)

    // If no return variable name was specified, generate a fresh one, then use the standard transaction processing rule.
    rule <k> processDecls(C, (transaction T(Args) returns RetType : S) Ds) => processDecls(C, (transaction T(Args) returns var(I) : RetType : S) Ds) ... </k>
        <freshCounter> I => I +Int 1 </freshCounter>
        [structural]

    rule <k> processDecls(C, (transaction T(Args) returns X : RetType : S) Ds) => processDecls(C, Ds) ... </k>
        <functions>
            ...
            C |-> functions(Funcs => Funcs (T |-> transaction(X : resolveType(C, RetType),
                                          resolveTypes(C, Args),
                                          resolveTypes(C, normalizeTxBody(X, normalize(S))))))
            ...
        </functions>
        [structural]

    syntax FuncData ::= view(Type, VarDefs, Expr)

    rule <k> processDecls(C, (view F(Args) returns RetType := E) Ds) => processDecls(C, Ds) ... </k>
        <functions>
            ...
            C |-> functions(Funcs => Funcs (F |-> view(resolveType(C, RetType),
                                              resolveTypes(C, Args),
                                              resolveTypes(C, normalizeExpr(E)))))
            ...
        </functions>
        [structural]

    // TODO: Implement this. It will translate to A-normal form, eliminate more complicated syntactic sugar, etc.
    syntax Expr ::= normalizeExpr(Expr) [function, functional]
    rule normalizeExpr(E) => E

    // TODO: It would be nice toa void inserting the unpacks if not necessary (i.e., no fields are accessed)
    syntax Stmt ::= normalizeTxBody(Var, Stmt) [function, functional]
    rule normalizeTxBody(_, A --[ Sel ]-> B) => unpackAll(fieldVars(varsStmt(A --[ Sel ]-> B))) (A --[ Sel ]-> B)
    rule normalizeTxBody(RetVar, var X : T := E in S:Stmt) => unpackAll(fieldVars(vars(E))) (var X : T := E in normalizeTxBody(RetVar, S))
    rule normalizeTxBody(_, pass) => pass
    rule normalizeTxBody(_, pack) => pack
    rule normalizeTxBody(_, unpack(F)) => unpack(F)
    rule normalizeTxBody(RetVar, return E) => unpackAll(fieldVars(vars(E))) (E --> RetVar) pack exit
    rule normalizeTxBody(_, exit) => pack exit
    rule normalizeTxBody(_, revert(E)) => unpackAll(fieldVars(vars(E))) revert(E) pack
    rule normalizeTxBody(_, F:FunctionCall) => unpackAll(fieldVars(vars(F))) F // TODO: Any other expressions we need to handle specially?
    rule normalizeTxBody(RetVar, if E { S1 } else { S2 } ) => unpackAll(fieldVars(vars(E))) (if E { normalizeTxBody(RetVar, S1) } else { normalizeTxBody(RetVar, S2) })
    rule normalizeTxBody(RetVar, try { S1 } catch (X : T) { S2 }) => try { normalizeTxBody(RetVar, S1) } catch (X : T) { normalizeTxBody(RetVar, S2) }
    rule normalizeTxBody(RetVar, S1:Stmt S2:Stmt) => normalizeTxBody(RetVar, S1) normalizeTxBody(RetVar, S2)

    syntax Stmt ::= unpackAll(Set) [function, functional]
    rule unpackAll(.Set) => pass
    rule unpackAll(SetItem(this . F) Rest) => unpack(F) unpackAll(Rest)

    syntax Stmt ::= normalize(Stmt) [function, functional]
    rule normalize(A --[ Sel ]-> B) => A --[ Sel ]-> B
    rule normalize(var X : T := E in S:Stmt) => var X : T := E in normalize(S)
    rule normalize((var X : T := E) S) => var X : T := E in normalize(S)
    rule normalize((var X : T := E)) => var X : T := E in pass
    rule normalize(pass) => pass
    rule normalize(pack) => pack
    rule normalize(exit) => exit
    rule normalize(unpack(F)) => unpack(F) // TODO: Need to unpack all fields before some statement, so do something like "=> unpackAll(fieldsUsedBy(S))". Will also need to keep track of what's already unpacked.
    rule normalize(return E) => return E
    rule normalize(revert(E)) => revert(E)
    // TODO: Pretty ugly...not sure if there's a better way to write this.
    rule normalize((F:Var(Args)):FunctionCall) => pack toANormal(Args, .Exprs, F)
    rule normalize( if E { S1 } else { S2 } ) => if E { normalize(S1) } else { normalize(S2) }
    rule normalize(try { S1 } catch (X : T) { S2 }) => try { normalize(S1) } catch (X : T) { normalize(S2) }
    rule normalize(S1:Stmt S2:Stmt) => normalize(S1) normalize(S2)
        requires (var _ : _ := _) :/=K S1

    syntax Stmt ::= toANormal(Exprs, Exprs, Var) [function, functional]
    rule toANormal(Args, _, F) => expr(F(Args))
    // TODO: This is basically right, except we need to be able to generate fresh variables in this function somehow.
    //     - Could make it an anywhere rule (probably bad for performance)
    //     - Could write some evaluation contexts (probably do this, even though it requires some restructuring)
    /* rule toANormal(.Exprs, Args, F) => expr(F(Args)) */
    /* // If it's a variable already, we don't need to change anything */
    /* rule toANormal((X:Var, Es):Exprs, Args, F) => toANormal(Es, (X, Args), F) */
    /* // If it's not a variable, generate a new variable for it. */
    /* rule toANormal((E, Es):Exprs, Args, F) => var X : ?_ := E in toANormal(Es, (X, Args), F) */
    /*     requires _:Var :/=K E */

    syntax Set ::= fieldVars(Set) [function, functional]

    rule fieldVars(.Set) => .Set
    rule fieldVars(SetItem(this.X) Rest) => SetItem(this.X) fieldVars(Rest)
    rule fieldVars(SetItem(A) Rest) => fieldVars(Rest)
        requires (this._) :/=K A

    syntax Set ::= varsStmt(Stmt) [function, functional]
                 | vars(FunctionCall) [function, functional]
                 | vars(Expr) [function, functional]
                 | vars(Selector) [function, functional]
                 | vars(Exprs) [function, functional]
                 | vars(Storage) [function, functional]

    rule varsStmt(A --[ Sel ]-> B) => vars(A) |Set vars(Sel) |Set vars(B)
    rule varsStmt(var _ : _ := E in S:Stmt) => vars(E) |Set varsStmt(S)
    rule varsStmt(pass) => .Set
    rule varsStmt(pack) => .Set
    rule varsStmt(unpack(_)) => .Set
    rule varsStmt(exit) => .Set
    rule varsStmt(S1:Stmt S2:Stmt) => varsStmt(S1) |Set varsStmt(S2)
    rule varsStmt(if B { S1:Stmt } else { S2:Stmt } ) => vars(B) |Set varsStmt(S1) |Set varsStmt(S2)

    rule vars(consume) => .Set
    rule vars(new _) => .Set

    rule vars(emptyval) => .Set
    rule vars(_:Int) => .Set
    rule vars(_:String) => .Set
    rule vars(_:Bool) => .Set
    rule vars(X:Var) => SetItem(X)
    rule vars(X.T) => SetItem(X.T)
    rule vars((new _(Args)):Expr) => vars(Args)

    rule vars(everything) => .Set
    rule vars(_:SelectorQuant _ : _ such that E) => vars(E)

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
    rule vars((if B { E1 } else { E2 }):IfExpr ) => vars(B) |Set vars(E1) |Set vars(E2)
    rule vars(let _ : _ := E in Body) => vars(E) |Set vars(Body)

    syntax Type ::= resolveType(Var, Type) [function]
    syntax BaseType ::= resolveType(Var, BaseType) [function]
    syntax VarDefs ::= resolveTypes(Var, VarDefs) [function]
    syntax Stmt ::= resolveTypes(Var, Stmt) [function]
    syntax Flow ::= resolveTypes(Var, Flow) [function]
    syntax Source ::= resolveTypes(Var, Source) [function]
    syntax Destination ::= resolveTypes(Var, Destination) [function]
    syntax Selector ::= resolveTypes(Var, Selector) [function]
    syntax Expr ::= resolveTypes(Var, Expr) [function]
    syntax Var ::= resolveTypes(Var, Var) [function]

    // Resolve types
    // TODO: Do this better...it's very repetitive and also just assumes all types are child types of the current contract, which may not be true.
    rule resolveType(_, nat) => nat
    rule resolveType(_, bool) => bool
    rule resolveType(_, string) => string
    rule resolveType(_, address) => address
    rule resolveType(_, unit) => unit
    rule resolveType(C, T:Var) => C.T
        requires T =/=K nat andBool T =/=K bool andBool T =/=K address andBool T =/=K string
    rule resolveType(_, X.T) => X.T
    rule resolveType(C, map K ==> V) => map resolveType(C, K) ==> resolveType(C, V)
    rule resolveType(C, linking K <=> V) => linking resolveType(C, K) <=> resolveType(C, V)
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
    rule resolveTypes(_, pass) => pass
    rule resolveTypes(_, pack) => pack
    rule resolveTypes(_, exit) => exit
    rule resolveTypes(_, unpack(X)) => unpack(X)

    // Resolve selector types
    rule resolveTypes(C, Q:SelectorQuant X : T:Type such that E) => Q X : resolveType(C, T) such that resolveTypes(C, E)
    rule resolveTypes(_, everything) => everything

    // Resolve expression types
    rule resolveTypes(_, I:Int) => I
    rule resolveTypes(_, S:String) => S
    rule resolveTypes(_, B:Bool) => B
    rule resolveTypes(_, emptyval) => emptyval
    rule resolveTypes(C, \ X : T . E) => \ X : resolveType(C, T) . resolveTypes(C, E)
    rule resolveTypes(_, X:Var) => X
    rule resolveTypes(C, X.Y) => resolveTypes(C, X) . resolveTypes(C, Y)
    // TODO: Finish all cases of resolveTypes

    // Resolve Storage types
    rule resolveTypes(_, consume) => consume
    // TODO: Need to handle the case that they actually do write C.T already by checking if the type resolves to a proper type name or not.
    //       Also need to put all the types into the type lookup table first, so that this function won't fail to find a declared type.
    //       Probably should warn if a type that doesn't exist/is in the wrong contract is referenced?
    rule resolveTypes(C, new T) => new C.T

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
    rule demote(nat) => nat
    rule demote(bool) => bool
    rule demote(string) => string
    rule demote(address) => address

    syntax Set ::= modifiers(BaseType) [function, functional]
    rule [[ modifiers(C.T) => Ms ]]
        <types> ... C |-> types((T |-> type(Ms, _)) _) ... </types>
    rule [[ modifiers(C) => Ms ]]
        <types> ... C |-> types((C |-> type(Ms, _)) _) ... </types>
    rule modifiers(_) => .Set [owise]
endmodule

