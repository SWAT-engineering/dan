module lang::dan::Checker

import lang::dan::Syntax;
import util::Math;

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

str prettyPrintAType(basicTy(integer())) = "int";
str prettyPrintAType(basicTy(string())) = "str";
str prettyPrintAType(basicTy(boolean())) = "bool";
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
     	c.define("<id>", consId(), id, defType(actualFormals, AType(Solver s) {
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
        void (Solver s) { s.requireSubtype(s.getType(expr), s.getType(ty), error(current, "Expression should be <ty>, found <prettyPrintAType(s.getType(expr))>")); });
}    

void collect(current:(DeclInStruct) `<Type ty> <DId id> <Arguments? args> <Size? size> <SideCondition? cond>`,  Collector c) {
	if ("<id>" != "_"){
		c.define("<id>", fieldId(), id, defType(ty));
	}
	collect(ty, c);
	currentScope = c.getScope();
	for (aargs <- args, a <- aargs.args){
		collect(a, c);
	}
	for (sz <-size){
		collect(sz.expr, c);
	}
	for (sc <- cond){
		collect(sc, c);
	}
	if (aargs <- args){
		c.require("constructor arguments", aargs, [ty] + aargs.args, void (Solver s) {
			s.requireTrue(tokenTy(refTy(_)):= s.getType(ty)  || listTy(tokenTy(refTy(_))) := s.getType(ty), error(aargs, "Constructor arguments only apply to user-defined types"));
			ty_ = top-down-break visit (ty){
				case (Type)`<Type t> []` => t
				case Type t => t
			};
			conId = fixLocation(parse(#Type, "<ty_>"), id@\loc);
			println(conId);
			ct = s.getTypeInType(s.getType(ty_), conId, {consId()}, currentScope);
			argTypes = atypeList([ s.getType(a) | a <- aargs.args ]);
			s.requireSubtype(ct.formals, argTypes, error(aargs, "Wrong type of arguments"));
		});
	}
	if (sz <- size){
		c.require("size argument", current, [ty] + [sz.expr], void (Solver s) {
			s.requireTrue(s.getType(ty) is listTy, error(current, "Setting size on a non-list element"));
			s.requireEqual(s.getType(sz.expr), basicTy(integer()), error(current, "Size must be an integer"));
		});
	}
	if (sc <- cond){
		switch(sc){
			case (SideCondition) `? ( <UnaryOperator uo> <Expr e> )`:{
				c.require("side condition", sc, [ty] + [e], void (Solver s) {
					s.requireEqual(s.getType(ty), s.getType(e), error(sc, "Unary expression in side condition must have the same type as declaration"));
				});
			}
			case (SideCondition) `? ( <Expr e> )`:{
				c.define("this", variableId(), current, defType(ty));
				c.require("side condition", sc, [e], void (Solver s) {
					s.requireEqual(s.getType(e), basicTy(boolean()), error(sc, "Side condition must be boolean"));
				});
			}
		}
	}
}

void collect(current:(SideCondition) `? ( <Expr e>)`, Collector c){
	collect(e, c);
}

void collect(current:(SideCondition) `? ( <UnaryOperator uo> <Expr e>)`, Collector c){
	collect(e, c);
}

void collect(current:(UnaryExpr) `<UnaryOperator uo> <Expr e>`, Collector c){
	collect(e, c);
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

void collect(current:(Type)`<Type t> [ ]`, Collector c) {
	collect(t, c);
	c.calculate("list type", current, [t], AType(Solver s) { return listTy(s.getType(t)); });
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

void collect(current: (Expr) `<HexIntegerLiteral nat>`, Collector c){
    c.fact(current, basicTy(integer()));
}

void collect(current: (Expr) `<NatLiteral nat>`, Collector c){
    c.fact(current, basicTy(integer()));
}

void collect(current: (Expr) `<Id id>`, Collector c){
    c.use(id, {variableId(), fieldId()});
}

void collect(current: (Expr) `<Expr e1> <UnaryOperator u> <Expr e2>`, Collector c){
    collect(e1, e2, c);
    c.require("binary expression", current, [e1, e2], void (Solver s) {
			s.requireEqual(s.getType(e1), s.getType(e2), error(current, "Operands must have the same type"));
			AType t = customCalculate(u, s.getType(e1), s);
			s.fact(current, t);
		});
}

void collect(current: (Expr) `<Expr e1> - <Expr e2>`, Collector c){
    collect(e1, e2, c);
    c.require("binary expression", current, [e1, e2], void (Solver s) {
			s.requireEqual(s.getType(e1), s.getType(e2), error(current, "Operands must have the same type"));
			s.requireEqual(s.getType(e1), basicTy(integer()), error(current, "Operands must be of type integer"));
			s.fact(current, basicTy(integer()));
		});
}


AType customCalculate((UnaryOperator) `==`, AType t, Solver s) = basicTy(boolean());

AType customCalculate(UnaryOperator uo, AType t, Solver s) = {
		s.requireEqual(t, basicTy(integer()), error(uo, "Comparator operands must act upon integers"));
		return basicTy(boolean());
	}
	when (UnaryOperator) `\>` := uo || (UnaryOperator) `\>=` := uo || (UnaryOperator) `\<` := uo || (UnaryOperator) `\<=` := uo;

	

// ----  Examples & Tests --------------------------------
TModel danTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config=getDanConfig(), debug=debug);
}

tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(tokenTy(refTy(str name))) = <true, name, {structId()}>;
tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(AType t) = <false, "", {}>;

private TypePalConfig getDanConfig() = tconfig(
    isSubType = danIsSubType,
    getTypeNameAndRole = danGetTypeNameAndRole,
    mayOverload = bool(set[loc] defs, map[loc, Define] defines){
    	// TODO do it just for the constructors 
    	return true;
    }
);

public Program sampleDan(str name) = parse(#Program, |project://dan-core/examples/<name>.dan|);

list[Message] runDan(str name, bool debug = false) {
    Tree pt = sampleDan(name);
    TModel tm = danTModelFromTree(pt, debug = debug);
    return tm.messages;
}
 
bool testDan(int n, bool debug = false) {
    return runTests([|project://dan-core/src/lang/dan/dan<util::Math::toString(n)>.ttl|], #start[Program], TModel (Tree t) {
        return danTModelFromTree(t, debug=debug);
    });
}

