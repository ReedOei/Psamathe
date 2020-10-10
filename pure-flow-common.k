module VARS
    imports DOMAINS-SYNTAX

    syntax Var ::= Id
                 | Var "." Id [klabel(qualified)]

    syntax Vars ::= List{Var, ","} [klabel(locators)]

    // Some special variables
    syntax Var ::= "bool" | "uint" | "address" | "string" | "nat"
    syntax Var ::= "this" | "msg" | "sender" | "key" | "value"
endmodule

module PURE-FLOW-COMMON-SYNTAX
    imports DOMAINS-SYNTAX
    imports VARS

    syntax Modifier ::= "fungible"
                      | "immutable"
                      | "unique"
                      | "consumable"
                      | "asset"
    syntax Modifiers ::= List{Modifier, ""}

    syntax TypeQuant ::= "one" | "any" | "nonempty" | "empty" | "every"
    syntax BaseType ::= Var
                      | "list" Type
                      | "map" Type "=>" Type
                      | "{" VarDefs "}"
                      | "record" "(" Vars ")" "{" VarDefs "}"
                      | "table" "(" Vars ")" Type
                      | "(" BaseType ")" [bracket]
    syntax QuantType ::= TypeQuant BaseType
    syntax Type ::= QuantType
                  | BaseType

    syntax VarDef ::= Var ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax RecordMember ::= VarDef "|->" Locator
                          | Var "|->" Locator
    syntax RecordMembers ::= List{RecordMember, ","}

    syntax Locator ::= Bool | Int | Var
                     | Locator "." Var [klabel(qualified)]
                     | "[" Locators "]"
                     | "[" Type ";" Locators "]"
                     | "{" RecordMembers "}"
                     | "record" "(" Vars ")" "{" RecordMembers "}"
                     | "demote" "(" Locator ")"
                     | "copy" "(" Locator ")"
                     | "var" Var ":" BaseType
                     | Locator "[" Locator "]"
                     | Locator "[" TypeQuant "such" "that" Var "(" Locators ")" "]"
                     | "(" Locator ")" [bracket]
                     | "consume"
    syntax Locators ::= List{Locator, ","} [klabel(locators), strict]
                      | Vars

    syntax Stmt ::= Locator "-->" Locator
                  | Locator "-->" Var "(" Locators ")" "-->" Locator
                  | Locator "-->" "new" Var "(" Locators ")" "-->" Locator
                  | Locator "--[" Locator "]->" Locator
                  | Locator "--[" TypeQuant "such" "that" Var "(" Locators ")" "]->" Locator
                  | Var "(" Locators ")" "-->" Locator
                  | "new" Var "(" Locators ")" "-->" Locator
                  | "try" "{" Stmts "}" "catch" "{" Stmts "}"
    syntax Stmts ::= List{Stmt, ""} [klabel(stmts)]

    syntax Decl ::= "#nopreprocess"
                  | "type" Id "is" Modifiers BaseType
                  | "transformer" Id "(" VarDefs ")" "->" VarDef "{" Stmts "}"
    syntax Decls ::= List{Decl, ""}

    syntax Program ::= Decls ";" Stmts

    // Expand out these types as abbreviations for special kinds of tables.
    rule (map T1:Type => T2:Type ) => table (key) one record(key) { key : T1, value : T2 } [macro-rec]

    rule list T => table (.Vars) T [macro-rec]

    rule { Fields:VarDefs } => record (.Vars) { Fields } [macro-rec]

    rule { Members:RecordMembers } => record (.Vars) { Members } [macro-rec]

    syntax Locator ::= lastLoc(Locators) [function, functional]
    rule lastLoc(L:Locator) => L
    rule lastLoc(_, B, Rest) => lastLoc(B, Rest)

    syntax Locators ::= initLocs(Locators) [function, functional]
    rule initLocs(_:Locator) => .Locators
    rule initLocs(A, B, Rest) => A, initLocs(B, Rest)

    // Expand syntactic sugar for flows
    rule A --[ L:Locator ]-> B => A[L] --> B [macro-rec]
    rule A --[ Q such that F(Args) ]-> B => A[Q such that F(Args)] --> B [macro-rec]
    rule (F:Var(Args:Locators) --> B):Stmt => lastLoc(Args) --> F(initLocs(Args)) --> B [macro-rec]
    rule new T(Args) --> B => lastLoc(Args) --> new T(initLocs(Args)) --> B [macro-rec]
endmodule

module PURE-FLOW-COMMON
    imports DOMAINS
    imports PURE-FLOW-COMMON-SYNTAX

    configuration
        <common>
            <k> preprocessProgram($PGM:Program) </k>
            <typeEnv> .Map </typeEnv>
            <types> .Map </types>
            <functions> .Map </functions>
        </common>

    syntax KItem ::= transformer(VarDef, VarDefs, Stmts)
                   | typeDef(Set, BaseType)

    rule Decls ; Stmts => Decls ~> Stmts

    rule .Decls => . [structural]
    rule D:Decl Decls => D ~> Decls [structural]

    syntax KItem ::= preprocessProgram(Program)
    rule preprocessProgram(.Decls ; Stmts) => preprocessStmts(.Map, Stmts) [structural]
    rule preprocessProgram(#nopreprocess Decls ; Stmts) => Decls ~> Stmts [structural]
    rule preprocessProgram(D:Decl Decls ; Stmts)
         => preprocessDecl(D) ~> preprocessProgram(Decls ; Stmts)
         requires D =/=K #nopreprocess
         [structural]

    syntax Decl ::= preprocessDecl(Decl) [function, functional]
    rule preprocessDecl(type T is Ms BaseT) => type T is Ms inferQuantities(BaseT) [structural]
    rule preprocessDecl(transformer F(FormalArgs) -> Ret { Body })
         => transformer F(inferEach(FormalArgs)) -> inferVarDef(Ret) {
                preprocessStmts(makeEnv(inferEach(Ret, FormalArgs)), Body)
            }

    syntax Stmts ::= preprocessStmts(Map, Stmts) [function, functional]
    rule preprocessStmts(_, .Stmts) => .Stmts

    rule preprocessStmts(Env, (A --> B) Rest)
         => (annotateLocator(A, flowType(typeof(Env, A), typeof(Env, B)))
             -->
             annotateLocator(B, flowType(typeof(Env, A), typeof(Env, B))))
            preprocessStmts(Env declaredVars(B), Rest)

    rule [[ preprocessStmts(Env, (A --> F(Args) --> B):Stmt Rest)
            => (annotateLocator(A, flowType(typeof(Env, A), some(baseTypeOf(lastVDef(FormalArgs)))))
                --> F(Args) -->
                annotateLocator(B, flowType(some(baseTypeOf(Ret)), typeof(Env, B))))
               preprocessStmts(Env declaredVars(B), Rest)
         ]]
         <functions> ... F |-> transformer(Ret, FormalArgs, _) ... </functions>

    rule [[ preprocessStmts(Env, (A --> new T(Args) --> B):Stmt Rest)
            => (annotateLocator(A, flowType(typeof(Env, A), some(baseTypeOf(lastVDef(getConstructorArgs(BaseT))))))
                --> new T(Args) -->
                annotateLocator(B, flowType(some(T), typeof(Env, B))))
               preprocessStmts(Env declaredVars(B), Rest)
         ]]
         <types> ... T |-> typeDef(_, BaseT) ... </types>

    rule preprocessStmts(Env, (try { S1 } catch { S2 }) Rest)
         => (try { preprocessStmts(Env, S1) } catch { preprocessStmts(Env, S2) })
            preprocessStmts(Env, Rest)

    syntax Locator ::= annotateLocator(Locator, BaseType) [function, functional]
    rule annotateLocator(I:Int, _) => I
    rule annotateLocator(B:Bool, _) => B
    rule annotateLocator(X:Var, _) => X
    rule annotateLocator([ Q T ; Ls ], _) => [ Q T ; annotateEach(Ls, T) ]:Locator
    rule annotateLocator([ Ls ], T) => [ inferQuantitiesType(T) ; annotateEach(Ls, T) ]:Locator
    rule annotateLocator(var X : T, _) => var X : inferQuantities(T)
    rule annotateLocator(record(Keys) { Members:RecordMembers }, record(_) { Fields })
         => record(Keys) { annotateEach(Members, Fields) }
    rule annotateLocator(L[K], _) => L[K]
    rule annotateLocator(L[K], map _ => _) => L[K].value
    rule annotateLocator(L[Q such that F(Args)], _) => L[Q such that F(Args)]
    rule annotateLocator(demote(L), _) => demote(L)
    rule annotateLocator(copy(L), _) => copy(L)
    rule annotateLocator(L.X, _) => L.X

    syntax Locators ::= annotateEach(Locators, BaseType) [function, functional]
    rule annotateEach(.Locators, _) => .Locators
    rule annotateEach((L:Locator, Ls), T) => annotateLocator(L, T), annotateEach(Ls, T)

    syntax RecordMembers ::= annotateEach(RecordMembers, VarDefs) [function, functional]
    rule annotateEach(.RecordMembers, .VarDefs) => .RecordMembers
    rule annotateEach((X : Q T |-> L, RestMembers), (_, RestDefs))
         => (X : Q T |-> annotateLocator(L, T)), annotateEach(RestMembers, RestDefs)
    rule annotateEach((X : T |-> L, RestMembers), (_, RestDefs))
         => (X : inferQuantitiesType(T) |-> annotateLocator(L, T)), annotateEach(RestMembers, RestDefs)
    rule annotateEach((X:Var |-> L, RestMembers), (_ : Q T, RestDefs))
         => (X : Q T |-> annotateLocator(L, T)), annotateEach(RestMembers, RestDefs)
    rule annotateEach((X:Var |-> L, RestMembers), (_ : T, RestDefs))
         => (X : inferQuantitiesType(T) |-> annotateLocator(L, T)), annotateEach(RestMembers, RestDefs)

    syntax MaybeType ::= some(BaseType) | "none"
                       | typeof(Map, Locator) [function, functional]
    rule typeof(_, _:Int) => some(nat)
    rule typeof(_, _:Bool) => some(bool)
    rule typeof((X |-> T) _, X:Var) => some(T)
    rule typeof((X |-> _ T) _, X:Var) => some(T)
    rule typeof((X |-> record(_) { Fields }) _, X.Y) => lookupType(Fields, Y)
    rule typeof((X |-> _ record(_) { Fields }) _, X.Y) => lookupType(Fields, Y)
    rule [[ typeof((X |-> _:TypeQuant T:Var) _, X.Y) => lookupType(Fields, Y) ]]
        <types> ... T |-> typeDef(_, record(_) { Fields }) ... </types>
    rule [[ typeof((X |-> T:Var) _, X.Y) => lookupType(Fields, Y) ]]
        <types> ... T |-> typeDef(_, record(_) { Fields }) ... </types>
    rule typeof(_, var _ : T) => some(inferQuantities(T))
    rule typeof(_, [ T ; _ ]) => some(list inferQuantitiesType(T))
    rule typeof(_, [ _ ]) => none
    rule typeof(_, record(Keys) { Members }) => some(record(Keys) { inferEach(membersToDefs(Members)) })
         requires allHaveType(Members)
    rule typeof(_, record(_) { Members}) => none
        requires notBool(allHaveType(Members))
    rule typeof(Env, demote(L)) => demoteMaybeType(typeof(Env, L))
    rule typeof(Env, copy(L)) => demoteMaybeType(typeof(Env, L))
    rule typeof(Env, L[_]) => typeof(Env, L)
    rule typeof(Env, L[_ such that _(_)]) => typeof(Env, L)

    syntax MaybeType ::= lookupType(VarDefs, Var) [function, functional]
    rule lookupType(.VarDefs, _) => none
    rule lookupType((X : _ T, _), X) => some(T)
    rule lookupType((X : T, _), X) => some(T)
    rule lookupType((Y : _, Rest), X) => lookupType(Rest, X)
        requires X =/=K Y

    syntax MaybeType ::= demoteMaybeType(MaybeType) [function, functional]
    rule demoteMaybeType(none) => none
    rule demoteMaybeType(some(T)) => some(demoteBaseType(T))

    syntax Bool ::= allHaveType(RecordMembers) [function, functional]
    rule allHaveType(.RecordMembers) => true
    rule allHaveType(_:VarDef |-> _, Rest) => allHaveType(Rest)
    rule allHaveType(_:Var |-> _, _) => false

    syntax BaseType ::= flowType(MaybeType, MaybeType) [function, functional]
    rule flowType(some(A), _) => A
    rule flowType(_, some(B)) => B

    // TODO: Should probably do a better job here
    syntax Map ::= declaredVars(Locator) [function, functional]
    rule declaredVars(var X : T) => X |-> T
    rule declaredVars(_) => .Map [owise]

    syntax QuantType ::= inferQuantitiesType(BaseType) [function, functional]
    rule inferQuantitiesType(nat) => any nat
    rule inferQuantitiesType(bool) => one bool
    rule inferQuantitiesType(string) => one string
    rule inferQuantitiesType(address) => one address
    rule inferQuantitiesType(record(Keys) { Fields }) => one record(Keys) { inferEach(Fields) }
    rule inferQuantitiesType(table(Keys) T) => any table(Keys) inferQuantitiesType(T)
    rule inferQuantitiesType(table(Keys) Q T) => any table(Keys) Q inferQuantities(T)
    rule [[ inferQuantitiesType(T) => any T ]]
        <types> ... T |-> typeDef(Ms, _) ... </types>
        requires fungible in Ms
    rule [[ inferQuantitiesType(T) => withBaseType(T, inferQuantitiesType(BaseT)) ]]
        <types> ... T |-> typeDef(Ms, BaseT) ... </types>
        requires notBool(fungible in Ms)

    syntax VarDef ::= inferVarDef(VarDef) [function, functional]
    rule inferVarDef(X : Q T) => X : Q T
    rule inferVarDef(X : T) => X : inferQuantitiesType(T)

    syntax VarDefs ::= inferEach(VarDefs) [function, functional]
    rule inferEach(.VarDefs) => .VarDefs
    rule inferEach(V:VarDef, Rest) => inferVarDef(V), inferEach(Rest)

    syntax QuantType ::= withBaseType(BaseType, QuantType) [function, functional]
    rule withBaseType(T, Q _) => Q T

    syntax BaseType ::= inferQuantities(BaseType) [function, functional]
    rule inferQuantities(nat) => nat
    rule inferQuantities(bool) => bool
    rule inferQuantities(string) => string
    rule inferQuantities(address) => address
    rule inferQuantities(record(Keys) { Fields }) => record(Keys) { inferEach(Fields) }
    rule inferQuantities(table(Keys) T) => table(Keys) inferQuantitiesType(T)
    rule inferQuantities(table(Keys) Q T) => table(Keys) Q inferQuantities(T)
    rule inferQuantities(T:Var) => T

    syntax QuantType ::= demoteType(QuantType) [function, functional]
    rule demoteType(Q:TypeQuant T) => Q demoteBaseType(T)

    syntax BaseType ::= demoteBaseType(BaseType) [function, functional]
    rule demoteBaseType(nat) => nat
    rule demoteBaseType(string) => string
    rule demoteBaseType(address) => address
    rule demoteBaseType(bool) => bool
    rule [[ demoteBaseType(T1) => demoteBaseType(BaseT) ]]
        <types> ... T1 |-> typeDef(_, BaseT) ... </types>
    rule demoteBaseType(table(Keys) Q T) => table(Keys) Q demoteBaseType(T)
    rule demoteBaseType(record(Keys) { Fields }) => record(Keys) { demoteVarDefs(Fields) }

    syntax VarDefs ::= demoteVarDefs(VarDefs) [function, functional]
    rule demoteVarDefs(.VarDefs) => .VarDefs
    rule demoteVarDefs(X : Q T, Rest) => X : Q demoteBaseType(T), demoteVarDefs(Rest)

    syntax VarDef ::= lastVDef(VarDefs) [function, functional]
    rule lastVDef(X : Q T) => X : Q T
    rule lastVDef(_:VarDef, X : Q T, Rest) => lastVDef(X : Q T, Rest)

    syntax BaseType ::= baseTypeOf(VarDef) [function, functional]
    rule baseTypeOf(_ : _ T) => T

    syntax VarDefs ::= tailVDefs(VarDefs) [function, functional]
    rule tailVDefs(.VarDefs) => .VarDefs
    rule tailVDefs(_:VarDef, Tail) => Tail

    syntax VarDefs ::= getConstructorArgs(BaseType) [function, functional]
    rule getConstructorArgs(nat) => !_:Id : any nat
    rule getConstructorArgs(string) => !_:Id : one string
    rule getConstructorArgs(bool) => !_:Id : one bool
    rule getConstructorArgs(address) => !_:Id : one address
    rule getConstructorArgs(table(Keys) Q T) => !_:Id : any table(Keys) Q T
    rule getConstructorArgs(record(_) { Fields }) => Fields

    syntax VarDefs ::= membersToDefs(RecordMembers) [function, functional]
    rule membersToDefs(.RecordMembers) => .VarDefs
    rule membersToDefs((X : T |-> _), Rest) => (X : T), membersToDefs(Rest)

    syntax List ::= remove(KItem, List) [function, functional]
    rule remove(_, .List) => .List
    rule remove(X, ListItem(X) Rest) => Rest
    rule remove(Y, ListItem(X) Rest) => ListItem(X) remove(Y, Rest)
        requires X =/=K Y

    syntax List ::= removeList(List, List) [function, functional]
    rule removeList(.List, Ys) => Ys
    rule removeList(ListItem(X) Xs, Ys) => removeList(Xs, remove(X, Ys))

    syntax Map ::= makeEnv(VarDefs) [function, functional]
    rule makeEnv(.VarDefs) => .Map
    rule makeEnv(X : Q T, Rest) => (X |-> Q T) makeEnv(Rest)

    syntax Locators ::= appendLoc(Locators, Locator) [function, functional]
    rule appendLoc(.Locators, K) => K
    rule appendLoc((L, Ls), K) => L, appendLoc(Ls, K)

    syntax Set ::= modifiersToSet(Modifiers) [function, functional]
    rule modifiersToSet(.Modifiers) => .Set
    rule modifiersToSet(M:Modifier Ms) => SetItem(M) modifiersToSet(Ms)

    syntax Bool ::= KItem "inList" List [function, functional]
    rule _ inList .List => false
    rule X inList (ListItem(X) _) => true
    rule X inList (ListItem(Y) Rest) => X inList Rest
        requires X =/=K Y

endmodule

