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

    syntax TypeQuant ::= "!" | "any" | "nonempty" | "empty" | "every"
    syntax BaseType ::= Var
                      | "list" Type
                      | "map" Type "=>" Type
                      | "{" VarDefs "}"
                      | "record" "(" Vars ")" "{" VarDefs "}"
                      | "table" "(" Vars ")" Type
                      | "(" BaseType ")" [bracket]
    syntax Type ::= TypeQuant BaseType

    syntax VarDef ::= Var ":" Type
    syntax VarDefs ::= List{VarDef, ","}

    syntax RecordMember ::= Var ":" Type "|->" Locator
    syntax RecordMembers ::= List{RecordMember, ","}

    syntax Locator ::= Bool | Int | Var
                     | Locator "." Var [klabel(qualified)]
                     | "[" Type ";" Locators "]"
                     | "record" "(" Vars ")" "{" RecordMembers "}"
                     | "{" RecordMembers "}"
                     | "demote" "(" Locator ")"
                     | "copy" "(" Locator ")"
                     | "var" Var ":" BaseType
                     | Locator "[" Locator "]"
                     | Locator "[" TypeQuant "such" "that" Var "(" Locators ")" "]"
                     | "(" Locator ")" [bracket]
    syntax Locators ::= List{Locator, ","} [klabel(locators), strict]
                      | Vars

    syntax Stmt ::= Locator "-->" Locator
                  | Locator "-->" Var "(" Locators ")" "-->" Locator
                  | Locator "-->" "new" Var "(" Locators ")" "-->" Locator
                  | "try" "{" Stmts "}" "catch" "{" Stmts "}"
    syntax Stmts ::= List{Stmt, ""} [klabel(stmts)]

    syntax Decl ::= "type" Id "is" Modifiers BaseType
                  | "transformer" Id "(" VarDefs ")" "->" VarDef "{" Stmts "}"
    syntax Decls ::= List{Decl, ""}

    syntax Program ::= Decls ";" Stmts

    // Expand out these types as abbreviations for special kinds of tables.
    rule (map T1 => T2) => table (key) ! record(key) { key : T1, value : T2 } [macro-rec]
    rule list T => table (.Vars) T [macro-rec]

    rule { Fields:VarDefs } => record (.Vars) { Fields } [macro-rec]

    rule { Members:RecordMembers } => record (.Vars) { Members } [macro-rec]
endmodule

module PURE-FLOW-COMMON
    imports DOMAINS
    imports PURE-FLOW-COMMON-SYNTAX

    configuration
        <common>
            <typeEnv> .Map </typeEnv>
            <types> .Map </types>
        </common>

    syntax Type ::= demoteType(Type) [function, functional]
    rule demoteType(Q:TypeQuant T) => Q demoteBaseType(T)

    syntax BaseType ::= demoteBaseType(BaseType) [function, functional]
    rule demoteBaseType(nat) => nat
    rule demoteBaseType(string) => string
    rule demoteBaseType(address) => address
    rule demoteBaseType(bool) => bool
    rule [[ demoteBaseType(T1) => demoteBaseType(T2) ]]
        <types> ... T1 |-> (type _ is _ T2) ... </types>
    rule demoteBaseType(table(Keys) Q T) => table(Keys) Q demoteBaseType(T)
    rule demoteBaseType({ Fields }) => { demoteVarDefs(Fields) }

    syntax VarDefs ::= demoteVarDefs(VarDefs) [function, functional]
    rule demoteVarDefs(.VarDefs) => .VarDefs
    rule demoteVarDefs(X : Q T, Rest) => X : Q demoteBaseType(T), demoteVarDefs(Rest)

    syntax BaseType ::= flowType(Locator, Locator) [function, functional]
    rule flowType(_:Int, _) => nat
    rule flowType(_, _:Int) => nat
    rule flowType(var _ : T, _) => T
    rule flowType(_, var _ : T) => T
    rule [[ flowType(X, _) => T ]]
        <typeEnv> ... X |-> T ... </typeEnv>
    rule [[ flowType(_, X) => T ]]
        <typeEnv> ... X |-> T ... </typeEnv>
    rule flowType(demote(A), B) => demoteBaseType(flowType(A, B))
    rule flowType(A, demote(B)) => demoteBaseType(flowType(A, B))
    rule flowType(copy(A), B) => demoteBaseType(flowType(A, B))
    rule flowType(A, copy(B)) => demoteBaseType(flowType(A, B))

    syntax VarDef ::= lastVDef(VarDefs) [function, functional]
    rule lastVDef(X : T) => X : T
    rule lastVDef(_ : _, X : T, Rest) => lastVDef(X : T, Rest)

    syntax BaseType ::= baseTypeOf(VarDef) [function, functional]
    rule baseTypeOf(_ : _ T) => T

    syntax VarDefs ::= tailVDefs(VarDefs) [function, functional]
    rule tailVDefs(.VarDefs) => .VarDefs
    rule tailVDefs(_ : _, Tail) => Tail

    syntax VarDefs ::= getConstructorArgs(BaseType) [function, functional]
    rule getConstructorArgs(nat) => !_:Id : any nat
    rule getConstructorArgs(string) => !_:Id : ! string
    rule getConstructorArgs(bool) => !_:Id : ! bool
    rule getConstructorArgs(address) => !_:Id : ! address
    rule getConstructorArgs(table(Keys) T) => !_:Id : any table(Keys) T
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
    rule makeEnv(X : T, Rest) => (X |-> T) makeEnv(Rest)

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

