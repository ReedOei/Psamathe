module YUL-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Identifier ::= Id | Identifier "." Identifier [left, assoc]
    syntax Identifiers ::= Identifier
                         | Identifiers "," Identifiers [right, assoc]

	syntax TypeName ::= Identifier

    syntax TypedIdentifier ::= Identifier ":" TypeName
                             // Weird, because there's no type, but the grammar allows it because there is a default type..."usually the integer word of the target machine"
                             // In the case of Ethereum, this is uint256.
                             | Identifier
    syntax TypedIdentifiers ::= TypedIdentifier
                              | TypedIdentifiers "," TypedIdentifiers [right, assoc]

	syntax Block ::= "{" "}" | "{" Statements "}"
	syntax Statement ::= Block
					   | FunctionDefinition
					   | VariableDeclaration
                       | Assignment
                       | If
                       | Expression
                       | Switch
                       | ForLoop
                       | BreakContinue
                       | Leave
    syntax Statements ::= Statement
                        | Statements Statements [right, assoc]
	syntax FunctionDefinition ::= "function" Identifier "(" TypedIdentifiers ")" "->" TypedIdentifiers Block
	                            | "function" Identifier "(" ")" "->" TypedIdentifiers Block
	                            | "function" Identifier "(" TypedIdentifiers ")" Block
	                            | "function" Identifier "(" ")" Block
	syntax VariableDeclaration ::= "let" TypedIdentifiers ":=" Expression
	                             | "let" TypedIdentifiers
	syntax Assignment ::= Identifiers ":=" Expression
	syntax Expression ::= FunctionCall | Identifier | Literal
    syntax Expressions ::= Expression
                         | Expressions "," Expressions [right, assoc]
	syntax If ::= "if" Expression Block
	syntax Switch ::= "switch" Expression Cases
	                | "switch" Expression Cases Default
	                | "switch" Expression Default
	syntax Case ::= "case" Literal Block
    syntax Cases ::= Case
                   | Case Cases
	syntax Default ::= "default" Block
	syntax ForLoop ::= "for" Block Expression Block Block
	syntax BreakContinue ::= "break" | "continue"
	syntax Leave ::= "leave"
	syntax FunctionCall ::= Identifier "(" Expressions ")"
	                      | Identifier "(" ")"
	syntax Literal ::= Int | String | Bool | HexNumber

    syntax Object ::= "object" String "{" Code ObjDatas "}"
                    | "object" String "{" Code "}"
    syntax Code ::= "code" Block
    syntax Data ::= "data" String String
    syntax ObjData ::= Object | Data
    syntax ObjDatas ::= ObjData
                      | ObjDatas "," ObjDatas [right, assoc]
    /* syntax Data ::= "data" String ( HexLiteral | StringLiteral ) */

    // From the Official documentation. We can add support for these if we end up needed them.
    // For now, we only care about the syntax of Yul insofar compiling our own language.
	/* syntax NumberLiteral = HexNumber | DecimalNumber */
	/* syntax HexLiteral = 'hex' ('"' ([0-9a-fA-F]{2})* '"' | '\'' ([0-9a-fA-F]{2})* '\'') */
	/* syntax StringLiteral = '"' ([^"\r\n\\] | '\\' .)* '"' */
	syntax HexNumber ::= r"0x[0-9a-fA-F]+" [token]
	/* syntax DecimalNumber = [0-9]+ */
endmodule

