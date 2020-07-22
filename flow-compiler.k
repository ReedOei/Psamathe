require "flow-common.k"
require "yul-syntax.k"

module FLOW-COMPILER-SYNTAX
    imports FLOW-SYNTAX
endmodule

module FLOW-COMPILER
    imports DOMAINS
    imports COLLECTIONS

    imports FLOW-COMPILER-SYNTAX
    imports FLOW-COMMON

    imports YUL-SYNTAX

    configuration
        <common />
        <objects> .List </objects>

    // NOTE: We just compile all the contracts, and ignore the global statements, which are only there for evaluation of the formal semantics.
    syntax CompileStmt ::= compile(Set)
    syntax Stmt ::= CompileStmt

    rule <k> S:Stmt => compile(Contracts) </k>
        <contracts> Contracts </contracts>
        requires _:CompileStmt :/=K S

    rule compile(.Set) => .
    rule <k> compile(SetItem(C) Rest) => compileContract(C, Types, Fields, Funcs) ~> compile(Rest) ... </k>
        <types> ... C |-> Types </types>
        <fields> ... C |-> Fields ... </fields>
        <functions> ... C |-> Funcs </functions>

    // Add some special Ethereum built-ins identifiers
    syntax Identifier ::= "caller"
                        | "return"
                        | "datasize"
                        | "datacopy"
                        | "sstore"
                        | "dataoffset"
                        | "revert"
                        | "selector"
                        | "div"
                        | "calldataload"
                        | "s"
    syntax CompileStmt ::= compileContract(Var, Set, Set, Set)
    rule <k> compileContract(C, _, _, _) => . ... </k>
        <objects> ... .List => ListItem(
            object Var2String(C) {
                code {
                    sstore(0, caller())
                    // Deploy the contract
                    datacopy(0, dataoffset("runtime"), datasize("runtime"))
                    return(0, datasize("runtime"))
                }
                object "runtime" {
                    code {
                        switch selector()
                        default {
                            revert(0, 0)
                        }

                        function selector() -> s {
                            s := div(calldataload(0), 0x100000000000000000000000000000000000000000000000000000000)
                        }
                    }
                }
            })
        </objects>

    syntax String ::= Var2String(Var) [function, functional]
    rule Var2String(X:Id) => Id2String(X)
    // TODO: Finish this.
endmodule

