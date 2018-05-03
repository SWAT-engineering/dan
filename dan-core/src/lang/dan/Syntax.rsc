module lang::dan::Syntax

extend lang::std::Layout;

keyword Reserved = "abstract" | "struct" | "choice" | "u8" | "u16" | "u32" | "u64";

start syntax Program =
	TopLevelDecl* declarations;

lexical Id =  ([a-z A-Z 0-9 _] !<< [a-z A-Z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _])\Reserved;

lexical DId = Id | "_";
	
syntax TopLevelDecl
	= "struct" Id Formals? Annos? "{" DeclInStruct* declarations "}"
	| "choice" Id Formals? Annos? "{" DeclInChoice* declarations "}"
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
	
syntax Formal = Type Id;
	
syntax Arguments
	= "(" {Expr ","}* args  ")"
	;
	
syntax Size
	= "[" Expr "]"
	;	
	
syntax ParserSpec
	= DId Arguments? Size? SideCondition?
	;	
	
syntax SideCondition 
	= "?" "(" Expr ")"
	| "?" "(" UnaryExpr ")"
	;
	
syntax ParserSpecInChoice
	= Type Arguments? Size?
	;		
	
syntax DeclInStruct
	= Type ParserSpec 
	| Type Id "=" Expr
	;
	
	
syntax Expr 
	= Id
	| NatLiteral
	| HexIntegerLiteral
	| StringLiteral
	| Id Arguments
	| "(" Expr ")"
	| "-" Expr
	> Expr "==" Expr
	| Expr "!=" Expr
	| Expr "\<=" Expr
	| Expr "\<" Expr
	| Expr "\>=" Expr
	| Expr "\>" Expr  
	> Expr "*" Expr
	> Expr "+" Expr
	| Expr "-" Expr
	> Expr "." Id
	| Expr "[" Range "]"
	;
		
	
syntax UnaryExpr
	= "==" Expr
	| "!=" Expr
	| "\<=" Expr
	| "\<" Expr
	| "\>=" Expr
	| "\>" Expr
	;  
	
syntax Range 
	 = ":" Expr
	 | Expr (":" Expr?)?
	 ;
	
syntax DeclInChoice
	= "abstract" Type Id
	| ParserSpecInChoice
	;

syntax AnonStruct
	= "struct" "{" DeclInStruct* declarations "}"
	;
	
syntax Type
	= Id
	| "u8"
	| "u16"
	| "u32"
	| "u64"
	| AnonStruct
	| Type "[" "]"
	;
	
lexical NatLiteral
	=  @category="Constant" [0-9]+ !>> [0-9]
	;

lexical HexIntegerLiteral
	=  [0] [X x] [0-9 A-F a-f]+ !>> [0-9 A-Z _ a-z] ;
	
lexical StringLiteral
	= @category="Constant" "\"" StringCharacter* chars "\"" ;	
	
lexical StringCharacter
	= "\\" [\" \' \< \> \\ b f n r t] 
	| UnicodeEscape 
	| ![\" \' \< \> \\]
	| [\n][\ \t \u00A0 \u1680 \u2000-\u200A \u202F \u205F \u3000]* [\'] // margin 
	;
	
lexical UnicodeEscape
	= utf16: "\\" [u] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] 
    | utf32: "\\" [U] (("0" [0-9 A-F a-f]) | "10") [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] // 24 bits 
    | ascii: "\\" [a] [0-7] [0-9A-Fa-f]
    ;
	