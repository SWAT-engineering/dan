module lang::dan::Syntax

extend lang::std::Layout;

keyword Reserved = "abstract" | "struct" | "choice";

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
	| AnonStruct
	| Type "[" "]"
	;
	

	
lexical Num
	= "-"? Nat
	;
	
lexical NatLiteral
	= [0-9]+ !>> [0-9]
	;

lexical HexIntegerLiteral
	= [0] [X x] [0-9 A-F a-f]+ !>> [0-9 A-Z _ a-z] ;
