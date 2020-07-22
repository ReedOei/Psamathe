require "flow-common.k"
require "yul-syntax.k"

module FLOW-COMPILER-SYNTAX
    imports FLOW-SYNTAX
endmodule

module KRYPTO
    imports STRING-SYNTAX
	syntax String ::= keccak256(String) [function, hook(KRYPTO.keccak256)]
endmodule

module FLOW-COMPILER
    imports DOMAINS
    imports COLLECTIONS

    imports FLOW-COMPILER-SYNTAX
    imports FLOW-COMMON

    imports KRYPTO

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
                        | "datasize" | "datacopy" | "dataoffset"
                        | "sstore"
                        | "revert"
                        | "selector"
                        | "div" | "add" | "mul"
                        | "calldataload" | "calldatasize"
			            | "decodeAsAddress" | "decodeAsUint"
                        | "iszero"
                        | "and" | "not"
                        | "mstore"
                        | "returnUint" | "returnTrue"
                        | "lt"
    // Add some variable names that we want to use below
    syntax Identifier ::= "s" | "v" | "pos" | "offset"
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
                object keccak256("test") {
                    code {
                        switch selector()
                        default {
                            revert(0, 0)
                        }

						// These utility functions taken from https://solidity.readthedocs.io/en/v0.6.11/yul.html
                        function selector() -> s {
                            s := div(calldataload(0), 0x100000000000000000000000000000000000000000000000000000000)
                        }

						function decodeAsAddress(offset) -> v {
                			v := decodeAsUint(offset)
                			if iszero(iszero(and(v, not(0xffffffffffffffffffffffffffffffffffffffff)))) {
                    			revert(0, 0)
                			}
            			}

            			function decodeAsUint(offset) -> v {
                			let pos := add(4, mul(offset, 0x20))
                			if lt(calldatasize(), add(pos, 0x20)) {
                    			revert(0, 0)
                			}
                			v := calldataload(pos)
            			}

						function returnUint(v) {
							mstore(0, v)
							return(0, 0x20)
						}

						function returnTrue() {
							returnUint(1)
						}
                    }
                }
            })
        </objects>

    syntax String ::= Var2String(Var) [function, functional]
    rule Var2String(X:Id) => Id2String(X)
    // TODO: Finish this.
endmodule

