module lang::dan::Checker

import lang::dan::Syntax;

extend analysis::typepal::TypePal;
extend analysis::typepal::TypePalConfig;

data AType
	= basicTy(PrimType primType)
	| listTy(AType ty)
	| tokenTy(TokenType tokenType)
	| topTy()
	;
	
data TokenType 
	= refTy(str name)
	| consType(AType formals)
	| anonTy(AType fields)
	| u8()
	| u16()
	| u32()
	| u64()
	;
	
data PrimType
	= integer()
	| string()
	| boolean()
	;
	
data IdRole
    = structId()
    | fieldId()
    | consId()
    ;
    	
bool danIsSubType(AType _, topTy()) = true;
bool danIsSubType(tokenTy(_), tokenTy("Token")) = true;
bool danIsSubType(AType t1, AType t2) = true
	when t1 == t2;
default bool danIsSubType(AType _, AType _) = false;

str prettyPrintAType(basicTy(integer())) = "integer";
str prettyPrintAType(basicTy(string())) = "string";
str prettyPrintAType(basicTy(boolean())) = "boolean";
str prettyPrintAType(listTy(_)) = "list";
str prettyPrintAType(tokenTy(refTy(name))) = "token " + name;
str prettyPrintAType(tokenTy(anonTy(_))) = "anonymous token";
str prettyPrintAType(tokenTy(u8())) = "u8 token";
str prettyPrintAType(tokenTy(u16())) = "u16 token";
str prettyPrintAType(tokenTy(u32())) = "u32 token";
str prettyPrintAType(tokenTy(u64())) = "u64 token";
str prettyPrintAType(topTy()) = "thing";


AType transType((Type) `<Id id>`) = tokenTy(refTy("<id>"));
AType transType((Type) `u8`) = tokenTy(u8());
AType transType((Type) `u16`) = tokenTy(u16());
AType transType((Type) `u32`) = tokenTy(u32());
AType transType((Type) `u64`) = tokenTy(u64());
AType transType((Type) `<AnonStruct as>`) = tokenTy(anonTy([]));
AType transType((Type) `<Type t> [ ]`) = listTy(transType(t));
AType transType((Type) `int`) = basicTy(integer());
AType transType((Type) `str`) = basicTy(string());
AType transType((Type) `bool`) = basicTy(boolean());

// ----  Collect definitions, uses and requirements -----------------------

void collect(current: (Program) `<TopLevelDecl* decls>`, Collector c){
    c.enterScope(current);
        collect(decls, c);
    c.leaveScope(current);
}
 
void collect(current:(TopLevelDecl) `struct <Id id> <Formals? formals> <Annos? annos> { <DeclInStruct* decls> }`,  Collector c) {
     c.define("<id>", structId(), id, defType(tokenTy(refTy("<id>"))));
     collect(id, formals, c);
     c.enterScope(current); {
     	collect(formals, c);
     	collect(decls, c);
    }
    c.leaveScope(current);
}

void collect(current:(Formal) `<Type ty> <Id id>`, Collector c){
	c.define("<id>", fieldId(), id, defType(transType(ty)));
}

list[AType] lookupConsTypeParameters(Collector c, Tree current, str id) {
	c.leaveScope(current);
	scope = c.getScope();
	c.enterScope(current);
    if ({<_, _, _,_, defType(consType(listType(pars)))>} <- getDefinitions(id, scope, {consId()})) {
    	return pars;
    }
    else {
        reportError(current, "Cannot find struct <id>");
    }
}

void collect(Id id, current:(Formals) `(<{Formal ","}* formals>)`, Collector c){
	c.define("<id>", consId(), id, defType(consType(listType([transType(f.typ) | Formal f <-formals]))));
	
}

void collect(current:(DeclInStruct) `<Type ty> <Id id> = <Expr expr>`,  Collector c) {
	c.define("<id>", fieldId(), id, defType(transType(ty)));
	collect(expr, c);
	c.require("good assignment", current, [expr],
        void (Solver s) { s.requireSubtype(s.getType(expr), transType(ty), error(current, "Expression should be `<transType(ty)>`, found <s.getType(expr)>")); });
}    

void collect(current:(DeclInStruct) `<Type ty> <DId id> <Arguments? args> <Size? size> <SideCondition? cond>`,  Collector c) {
	c.use(ty, { consId(), structId() });
	if ("<id>" != "_"){
		c.define("<id>", fieldId(), id, defType(transType(ty)));
	}
   	collect(args, c);
	//returnType = useClassType(scope, cons.id);
    c.require("arguments in <args>", current, [arg | arg <- args],
         void (Solver s) { 
         	if ({_, consType(listType(pars)), _} := s.getType(ty)){
         	    s.requireEquals(size(pars), size(args), "Formal and actual parameters have different sizes.");
         		for (<arg, p> <- args <- pars)
         	 		 s.requireSubtype(getType(arg), p, "Argument <arg> has incorrect type.");            	
         	}else{
         		throw error(current, "<ty> has not been declared as a struct.");
         	};
		 }); 
}

void collect(current: (Expr) `<StringLiteral lit>`, Collector c){
    c.fact(current, basicTy(string()));
}

void collect(current: (Expr) `<NatLiteral nat>`, Collector c){
    c.fact(current, basicTy(integer()));
}

void collect(current: (Expr) `<Id id>`, Collector c){
    // TODO
}

// ----  Examples & Tests --------------------------------
TModel danTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config=getDanConfig(), debug=debug);
}

private TypePalConfig getDanConfig() = tconfig(
    isSubType = danIsSubType
);

public Program sampleDan(str name) = parse(#Program, |project://dan-core/examples/<name>.dan|);

list[Message] runDan(str name, bool debug = false) {
    Tree pt = sampleDan(name);
    TModel tm = danTModelFromTree(pt, debug);
    return tm.messages;
}
