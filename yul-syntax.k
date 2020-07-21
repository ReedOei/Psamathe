module YUL-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Identifier ::= Id | Identifier "." Identifier [left, assoc]
    syntax Identifiers ::= List{Identifier, ","}

	syntax TypeName ::= Identifier

    syntax TypedIdentifier ::= Identifier ":" TypeName
                             // Weird, because there's no type, but the grammar allows it because there is a default type..."usually the integer word of the target machine"
                             // In the case of Ethereum, this is uint256.
                             | Identifier
    syntax TypedIdentifiers ::= List{TypedIdentifier, ","}

	syntax Block ::= "{" Stmts "}"
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
	syntax FunctionDefinition ::= "function" Identifier "(" TypedIdentifiers ")" "->" TypedIdentifiers Block
	                            | "function" Identifier "(" TypedIdentifiers ")" Block
	syntax VariableDeclaration ::= "let" TypedIdentifiers ":=" Expression
	                             | "let" TypedIdentifiers
	syntax Assignment ::= Identifiers ":=" Expression
	syntax Expression ::= FunctionCall | Identifier | Literal
    syntax Expressions ::= List{Expression, ","}
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
	syntax Leave = "leave"
	syntax FunctionCall = Identifier "(" Expressions ")"
	syntax Literal = Int | String | Bool

    // From the Official documentation. We can add support for these if we end up needed them.
    // For now, we only care about the syntax of Yul insofar compiling our own language.
		/* (NumberLiteral | StringLiteral | HexLiteral | TrueLiteral | FalseLiteral) ( ':' TypeName )? */
	/* syntax NumberLiteral = HexNumber | DecimalNumber */
	/* syntax HexLiteral = 'hex' ('"' ([0-9a-fA-F]{2})* '"' | '\'' ([0-9a-fA-F]{2})* '\'') */
	/* syntax StringLiteral = '"' ([^"\r\n\\] | '\\' .)* '"' */
	/* syntax TrueLiteral = 'true' */
	/* syntax FalseLiteral = 'false' */
	/* syntax HexNumber = '0x' [0-9a-fA-F]+ */
	/* syntax DecimalNumber = [0-9]+ */
endmodule

