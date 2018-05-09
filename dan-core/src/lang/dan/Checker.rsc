module lang::dan::Checker

import lang::dan::Syntax;

extend analysis::typepal::TypePal;
extend analysis::typepal::TypePalConfig;

data AType
	= basicTy(PrimType primType)
	| listTy(AType ty)
	| tokenTy(TokenType tokenType)
	| consTy(AType formals)
	| topTy()
	;
	
data TokenType 
	= refTy(str name)
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
bool danIsSubType(tokenTy(_), tokenTy(refTy("Token"))) = true;
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
 
Tree fixLocation(Tree tr, loc newLoc) =
	visit(tr) {
		case Tree t => t[@\loc = relocate(t@\loc,newLoc)]
        	when t has \loc
	 }; 
 
void collect(current:(TopLevelDecl) `struct <Id id> <Formals? formals> <Annos? annos> { <DeclInStruct* decls> }`,  Collector c) {
     c.define("<id>", structId(), current, defType(tokenTy(refTy("<id>"))));
     //collect(id, formals, c);
     c.enterScope(current); {
     	actualFormals = [af | f <- formals, af <- f.formals];
     	c.define("__<id>", consId(), id, defType(actualFormals, AType(Solver s) {
     		return consTy(atypeList([s.getType(a) | a <- actualFormals]));
     	}));
     	collect(actualFormals, c);
     	
     	collect(decls, c);
    }
    c.leaveScope(current);
}

void collect(current:(Formal) `<Type ty> <Id id>`, Collector c){
	c.define("<id>", fieldId(), current, defType(ty));
	collect(ty, c);
}

void collect(current:(DeclInStruct) `<Type ty> <Id id> = <Expr expr>`,  Collector c) {
	c.define("<id>", fieldId(), id, defType(ty));
	collect(ty, c);
	collect(expr, c);
	c.require("good assignment", current, [expr],
        void (Solver s) { s.requireSubtype(s.getType(expr), s.getType(ty), error(current, "Expression should be `<transType(ty)>`, found <s.getType(expr)>")); });
}    

void collect(current:(DeclInStruct) `<Type ty> <DId id> <Arguments args> <Size? size> <SideCondition? cond>`,  Collector c) {
	if ("<id>" != "_"){
		c.define("<id>", fieldId(), id, defType(ty));
	}
	collect(ty, c);
	currentScope = c.getScope();
	
	c.require("check constructor args", id, [ty] + [a | a<- args.args], void (Solver s) {
		s.requireTrue(s.getType(ty) is tokenTy, error(current, "You can only"));
		conId = fixLocation(parse(#Type, "__<ty>"), id@\loc);
		ct = s.getTypeInType(s.getType(ty), conId, {consId()}, currentScope);
		argTypes = atypeList([ s.getType(a) | a <- args.args ]);
		s.requireSubtype(ct.formals, argTypes, error(current, "wrong subtyping"));
	});
	
	collect(ty, args, c);
}

void collect(current:(Type)`u8`, Collector c) {
	c.fact(current, tokenTy(u8()));
}

void collect(current:(Type)`str`, Collector c) {
	c.fact(current, basicTy(string()));
}

void collect(current:(Type)`bool`, Collector c) {
	c.fact(current, basicTy(boolean()));
}  

void collect(current:(Type)`int`, Collector c) {
	c.fact(current, basicTy(integer()));
}  

void collect(current:(Type)`<Id i>`, Collector c) {
	c.use(i, {structId()}); 
} 


void collect(current:(DeclInStruct) `<Type ty> <DId id> <Size? size> <SideCondition? cond>`,  Collector c) {
	c.use(ty, { consId(), structId() });
	if ("<id>" != "_"){
		c.define("<id>", fieldId(), id, defType(transType(ty)));
	}

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

tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(tokenTy(refTy(str name))) = <true, name, {structId()}>;
tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(AType t) = <false, "", {}>;

private TypePalConfig getDanConfig() = tconfig(
    isSubType = danIsSubType,
    getTypeNameAndRole = danGetTypeNameAndRole
);

public Program sampleDan(str name) = parse(#Program, |project://dan-core/examples/<name>.dan|);

list[Message] runDan(str name, bool debug = false) {
    Tree pt = sampleDan(name);
    TModel tm = danTModelFromTree(pt, debug);
    return tm.messages;
}
