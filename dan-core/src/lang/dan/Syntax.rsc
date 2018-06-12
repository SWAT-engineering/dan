module lang::dan::Syntax

extend lang::std::Layout;

// TODO can we specify a pattern for u? types
keyword Reserved = "abstract" | "struct" | "choice"  | "int" | "str" | "bool" | "typ" | "module" | "import" | "while"  | "this" | "it";

start syntax Program =
	"module" Id
	Import* imports
	TopLevelDecl* declarations;

lexical Id 
	=  (([a-z A-Z 0-9 _] - [u]) !<< ([a-z A-Z] - [u])[a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Reserved 
	| @category="Constant" "this" 
	| @category="Constant" "it"
	// the following two productions make sure Id is not ambigious with UInt production
	| [u] !>> [a-z A-Z _] // a single u
	| ([u] [a-z A-Z _][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Reserved // or a u not followed by a number
	;

lexical DId = Id | "_";

syntax Import
	= "import" Id
	;
	
syntax TopLevelDecl
	= "struct" Id Formals? Annos? "{" DeclInStruct* declarations "}"
	| "choice" Id Formals? Annos? "{" DeclInChoice* declarations "}"
	| Type Id Formals? 
	;
	
syntax Annos 
	= "@" "(" {Anno "," }* annos ")"
	;	
	
syntax Anno
	= Id "=" Expr 
	;	
	
syntax Formals
	= "(" {Formal "," }* formals  ")"
	;
	
syntax Formal = Type typ Id id;
	
syntax Arguments
	= "(" {Expr ","}* args  ")"
	;
	
syntax Size
	= "[" Expr expr "]"
	;	
		
syntax SideCondition 
	= "?" "(" Expr ")"
	| "?" "(" UnaryExpr ")"
	| "while" "(" Expr ")"
	;
	
	
syntax DeclInStruct
	= Type DId Arguments? Size? SideCondition? 
	| Type Id "=" Expr
	;
	
	
// precedance and associativity based on Java
// as described here: https://introcs.cs.princeton.edu/java/11precedence/
syntax Expr 
	= NatLiteral
	| HexIntegerLiteral
	| StringLiteral
	| Id
	| bracket "(" Expr ")"
	| Id Arguments
	> Expr "[" Range "]"
	| Expr "." Id
	> "-" Expr
	| "!" Expr
	> left (
		  Expr "*" Expr
		| Expr "/" Expr
		| Expr "%" Expr
	)
	> left (
		  Expr "+" !>> [+] Expr
		| Expr "-" Expr
		| Expr "++" Expr
	)
	> left( 
		  Expr "\>\>" Expr
		| Expr "\<\<" Expr
		| Expr "\>\>\>" Expr
	)
	> non-assoc Expr ComparatorOperator Expr
	> left (
		  Expr "==" Expr
		| Expr "!=" Expr
	)
	> left Expr "&" Expr
	> left Expr "^" Expr
	> left Expr "|" Expr
	> left Expr "&&" Expr
	> left Expr "||" Expr
	> right Expr "?" Expr ":" Expr
	;
		
lexical ComparatorOperator
	= "\<="
	| "\<"
	| "\>="
	| "\>"
	;   	
	
lexical UnaryOperator
	= ComparatorOperator
	| "=="
	| "!="
	;
	
syntax UnaryExpr
	= UnaryOperator Expr e
	;  
	
syntax Range 
	 = ":" Expr
	 | Expr (":" Expr?)?
	 ;
	
syntax DeclInChoice
	= "abstract" Type Id
	| Type Arguments? Size?
	;

syntax AnonStruct
	= "struct" "{" DeclInStruct* declarations "}"dime
	;
	
syntax Type
	= Id
	| "int"
	| "str"
	| "bool"
	| "typ"
	| UInt
	| AnonStruct
	| Type "[" "]"
	;
	
lexical UInt = @category="Constant" "u" [0-9]+ !>> [0-9];
	
lexical NatLiteral
	=  @category="Constant" [0-9]+ !>> [0-9]
	;

lexical HexIntegerLiteral
	=  [0] [X x] [0-9 A-F a-f]+ !>> [0-9 A-Z _ a-z] ;
	
lexical StringLiteral
	= @category="Constant" "\"" StringCharacter* chars "\"" ;	
	
lexical StringCharacter
	= "\\" [\" \\ b f n r t] 
	| ![\" \\]
	| UnicodeEscape 
	;
	
lexical UnicodeEscape
	= utf16: "\\" [u] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] 
	| utf32: "\\" [U] (("0" [0-9 A-F a-f]) | "10") [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] // 24 bits 
	| ascii: "\\" [a] [0-7] [0-9A-Fa-f]
	;


