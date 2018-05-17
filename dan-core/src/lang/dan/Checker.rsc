module lang::dan::Checker

import lang::dan::Syntax;
import util::Math;
import ListRelation;
import Set;

extend analysis::typepal::TypePal;
extend analysis::typepal::TypePalConfig;


data AType
	= intType()
	| strType()
	| boolType()
	| listType(AType ty)
	| consType(AType formals)
	| refType(str name)
	| anonType(lrel[str, AType] fields)
	| u8()
	| u16()
	| u32()
	| u64()
	;
	
data IdRole
    = structId()
    | fieldId()
    | consId()
    ;
    	
//bool danIsSubType(AType _, topTy()) = true;
//bool danIsSubType(_), refType("Token"))) = true;
//bool danIsSubType(AType t1, AType t2) = true
//	when t1 == t2;
//default bool danIsSubType(AType _, AType _) = false;

bool isConvertible(u8(), intType()) = true;
bool isConvertible(u8(), strType()) = true;
bool isConvertible(u16(), intType()) = true;
bool isConvertible(u16(), strType()) = true;
bool isConvertible(u32(), intType()) = true;
bool isConvertible(u32(), strType()) = true;
bool isConvertible(u64(), intType()) = true;
bool isConvertible(u64(), strType()) = true;
bool isConvertible(listType(t), intType()) = danIsSubType(t, intType());
bool isConvertible(listType(t), strType()) = danIsSubType(t, strType());


bool isConvertible(AType t1, AType t2) = true
	when t1 == t2;
default bool isConvertible(AType _, AType _) = false;



str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(boolType()) = "bool";
str prettyPrintAType(listType(_)) = "list";
str prettyPrintAType(refType(name)) = "token " + name;
str prettyPrintAType(anonType(_)) = "anonymous token";
str prettyPrintAType(u8()) = "u8 token";
str prettyPrintAType(u16()) = "u16 token";
str prettyPrintAType(u32()) = "u32 token";
str prettyPrintAType(u64()) = "u64 token";


AType transType((Type) `<Id id>`) = refType("<id>");
AType transType((Type) `u8`) = u8();
AType transType((Type) `u16`) = u16();
AType transType((Type) `u32`) = u32();
AType transType((Type) `u64`) = u64();
AType transType((Type) `<AnonStruct as>`) = anonType([]);
AType transType((Type) `<Type t> [ ]`) = listType(transType(t));
AType transType((Type) `int`) = intType();
AType transType((Type) `str`) = strType();
AType transType((Type) `bool`) = boolType();

bool isTokenType(u8()) = true;
bool isTokenType(u16()) = true;
bool isTokenType(u32()) = true;
bool isTokenType(u64()) = true;
bool isTokenType(refType(_)) = true;
bool isTokenType(anonType(_)) = true;
bool isTokenType(listType(t)) = isTokenType(t); 
default bool isTokenType(AType t) = false;

bool isAssignableToInteger(intType()) = true;
bool isAssignableToInteger(u8()) = true;
bool isAssignableToInteger(u16()) = true;
bool isAssignableToInteger(u32()) = true;
bool isAssignableToInteger(u64()) = true;
bool isAssignableToInteger(listType(t)) = false 
	when t !:= intType();
default bool isAssignableToInteger(AType _) = false;

AType infixComparator(intType(), intType()) = boolType();
AType infixComparator(u8(), intType()) = boolType();
AType infixComparator(u8(), u8()) = boolType();
AType infixComparator(intType(), u8()) = boolType();
AType infixComparator(u16(), intType()) = boolType();
AType infixComparator(u16(), 16()) = boolType();
AType infixComparator(intType(), u16()) = boolType();
default AType infixComparator(AType t1, AType t2){ throw "Wrong operands for a comparator"; }

AType infixEquality(intType(), intType()) = boolType();
AType infixEquality(u8(), intType()) = boolType();
AType infixEquality(u8(), u8()) = boolType();
AType infixEquality(intType(), u8()) = boolType();
AType infixEquality(u16(), intType()) = boolType();
AType infixEquality(u16(), 16()) = boolType();
AType infixEquality(intType(), u16()) = boolType();
AType infixEquality(AType t1, AType t2) = boolType()
	when t1 == t2;
default AType infixEquality(AType t1, AType t2){ throw "Wrong operands for equality"; }

AType infixArithmetic(intType(), intType()) = intType();
AType infixArithmetic(u8(), intType()) = intType();
AType infixArithmetic(u8(), u8()) = intType();
AType infixArithmetic(intType(), u8()) = intType();
AType infixArithmetic(u16(), intType()) = intType();
AType infixArithmetic(u16(), 16()) = intType();
AType infixArithmetic(intType(), u16()) = intType();
default AType infixArithmetic(AType t1, AType t2){ throw "Wrong operands for an arithmetic operation"; }


// ----  Collect definitions, uses and requirements -----------------------

data Global = global(loc scope); 

Global global = global(|project://dummy.dummy|);

void collect(current: (Program) `<TopLevelDecl* decls>`, Collector c){
    c.enterScope(current);
    currentScope = c.getScope();
    global.scope = currentScope;
    	collect(decls, c);
    c.leaveScope(current);
}
 
Tree fixLocation(Tree tr, loc newLoc) =
	visit(tr) {
		case Tree t => t[@\loc = relocate(t@\loc,newLoc)]
        	when t has \loc
	 }; 
	 

 
void collect(current:(TopLevelDecl) `struct <Id id> <Formals? formals> <Annos? annos> { <DeclInStruct* decls> }`,  Collector c) {
     c.define("<id>", structId(), current, defType(refType("<id>")));
     //collect(id, formals, c);
     c.enterScope(current); {
     	actualFormals = [af | f <- formals, af <- f.formals];
     	c.define("<id>", consId(), id, defType(actualFormals, AType(Solver s) {
     		return consType(atypeList([s.getType(a) | a <- actualFormals]));
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
	c.require("declared type", ty, [ty], void(Solver s){
		s.requireTrue(isTokenType(s.getType(ty)), error(ty, "Non-initialized fields must be of a token type"));
	});
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
			s.requireTrue(refType(_) := s.getType(ty)  || listType(refType(_)) := s.getType(ty), error(aargs, "Constructor arguments only apply to user-defined types"));
			ty_ = top-down-break visit (ty){
				case (Type)`<Type t> []` => t
				case Type t => t
			};
			conId = fixLocation(parse(#Type, "<ty_>"), id@\loc);
			ct = s.getTypeInType(s.getType(ty_), conId, {consId()}, currentScope);
			argTypes = atypeList([ s.getType(a) | a <- aargs.args ]);
			s.requireSubtype(ct.formals, argTypes, error(aargs, "Wrong type of arguments"));
		});
	}
	if (sz <- size){
		c.require("size argument", current, [ty] + [sz.expr], void (Solver s) {
			s.requireTrue(s.getType(ty) is listType, error(current, "Setting size on a non-list element"));
			s.requireEqual(s.getType(sz.expr), intType(), error(current, "Size must be an integer"));
		});
	}
	if (sc <- cond){
		switch(sc){
			case (SideCondition) `? ( <UnaryOperator uo> <Expr e> )`:{
				c.require("side condition", sc, [e], void (Solver s) {
					s.requireTrue(isAssignableToInteger(s.getType(e)), error(sc, "Expression in unary side condition must have numeric type"));
				});
				//c.requireEqual(ty, e, error(sc, "Unary expression in side condition must have the same type as declaration"));
			}
			case (SideCondition) `? ( <Expr e> )`:{
				c.define("this", variableId(), current, defType(ty));
				c.require("side condition", sc, [e], void (Solver s) {
					s.requireEqual(s.getType(e), boolType(), error(sc, "Side condition must be boolean"));
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
	c.fact(current, u8());
}

void collect(current:(Type)`str`, Collector c) {
	c.fact(current, strType());
}

void collect(current:(Type)`bool`, Collector c) {
	c.fact(current, boolType());
}  

void collect(current:(Type)`int`, Collector c) {
	c.fact(current, intType());
}  

void collect(current:(Type)`<Id i>`, Collector c) {
	c.use(i, {structId()}); 
} 

void collect(current:(Type)`struct { <DeclInStruct* decls>}`, Collector c) {
	c.enterScope(current);
		collect(decls, c);
	c.leaveScope(current);
	ts =for (d <-decls){
			switch(d){
				case (DeclInStruct) `<Type t> <Id id> = <Expr e>`: append(t);
				case (DeclInStruct) `<Type t> <DId id> <Arguments? args> <Size? size> <SideCondition? sc>`: append(t);
			};
		};
	c.calculate("anonymous struct type", current, ts, AType(Solver s){
		fields = for (d <-decls){
			switch(d){
				case (DeclInStruct) `<Type t> <Id id> = <Expr e>`: append(<"<id>", s.getType(t)>);
				case (DeclInStruct) `<Type t> <DId id> <Arguments? args> <Size? size> <SideCondition? sc>`:  append(<"<id>", s.getType(t)>);
			};
		};
		return anonType(fields);
	});
} 

void collect(current:(TopLevelDecl) `struct <Id id> <Formals? formals> <Annos? annos> { <DeclInStruct* decls> }`,  Collector c) {
     c.define("<id>", structId(), current, defType(refType("<id>")));
     //collect(id, formals, c);
     c.enterScope(current); {
     	actualFormals = [af | f <- formals, af <- f.formals];
     	c.define("<id>", consId(), id, defType(actualFormals, AType(Solver s) {
     		return consType(atypeList([s.getType(a) | a <- actualFormals]));
     	}));
     	collect(actualFormals, c);
     	
     	collect(decls, c);
    }
    c.leaveScope(current);
}

void collect(current:(Type)`<Type t> [ ]`, Collector c) {
	collect(t, c);
	c.calculate("list type", current, [t], AType(Solver s) { return listType(s.getType(t)); });
}  


void collect(current:(DeclInStruct) `<Type ty> <DId id> <Size? size> <SideCondition? cond>`,  Collector c) {
	c.use(ty, { consId(), structId() });
	if ("<id>" != "_"){
		c.define("<id>", fieldId(), id, defType(transType(ty)));
	}

}

void collect(current: (Expr) `<StringLiteral lit>`, Collector c){
    c.fact(current, strType());
}

void collect(current: (Expr) `<HexIntegerLiteral nat>`, Collector c){
    c.fact(current, intType());
}

void collect(current: (Expr) `<NatLiteral nat>`, Collector c){
    c.fact(current, intType());
}

void collect(current: (Expr) `<Id id>`, Collector c){
    c.use(id, {variableId(), fieldId()});
}

void collect(current: (Expr) `<Expr e>.offset`, Collector c){
	collect(e, c);
	c.require("offset type", current, [e], void (Solver s) {
		s.requireTrue(isTokenType(s.getType(e)), error(current, "Only token types have offsets"));
	}); 
	c.fact(current, intType());
}

void collect(current: (Expr) `<Expr e>[ : <Expr end >]`, Collector c){
	collect(e, end, c);
	c.calculate("range", current, [e, end], AType (Solver s){
		s.requireTrue(listType(_) := s.getType(e), error(e, "Expression must be of list type"));
		s.requireEqual(end, intType(), error(end, "Indexes must be integers"));
		return s.getType(e);
	});
}

void collect(current: (Expr) `<Expr e>[ <Expr begin> : <Expr end >]`, Collector c){
	collect(e, begin, end, c);
	c.calculate("range", current, [e, begin, end], AType (Solver s){
		s.requireTrue(listType(_) := s.getType(e), error(e, "Expression must be of list type"));
		s.requireEqual(begin, intType(), error(begin, "Indexes must be integers"));
		s.requireEqual(end, intType(), error(end, "Indexes must be integers"));
		return s.getType(e);
	});
}

void collect(current: (Expr) `<Expr e>[ <Expr begin> : ]`, Collector c){
	collect(e, begin, c);
	c.calculate("range", current, [e, begin, end], AType (Solver s){
		s.requireTrue(listType(_) := s.getType(e), error(e, "Expression must be of list type"));
		s.requireEqual(begin, intType(), error(begin, "Indexes must be integers"));
		return listType(s.getType(e));
	});
}
	
void collect(current: (Expr) `<Expr e>[ <Expr idx>]`, Collector c){
	collect(e, idx, c);
	c.calculate("range", current, [e, idx], AType (Solver s){
		s.requireTrue(listType(_) := s.getType(e), error(e, "Expression must be of list type"));
		s.requireEqual(idx, intType(), error(idx, "Indexes must be integers"));
		listType(ty) = s.getType(e);
		return ty;
	});	
}

void collect(current: (Expr) `<Expr e>.<Id field>`, Collector c){
	collect(e, c);
	//currentScope = c.getScope();
	c.useViaType(e, field, {fieldId()});
	c.fact(current, field);
	//c.calculate("field type", current, [e], AType(Solver s) {
	//	return s.getTypeInType(s.getType(e), field, {fieldId()}, currentScope); });

}

void collect(current: (Expr) `<Expr e1> == <Expr e2>`, Collector c){
    collect(e1, e2, c);
    collectInfixOperation(current, "==", infixEquality, e1, e2, c); 
}

void collect(current: (Expr) `<Expr e1> <UnaryOperator u> <Expr e2>`, Collector c){
    collect(e1, e2, c);
    collectInfixOperation(current, "<u>", infixComparator, e1, e2, c); 
}

void collect(current: (Expr) `<Expr e1> + <Expr e2>`, Collector c){
    collect(e1, e2, c);
    collectInfixOperation(current, "+", infixArithmetic, e1, e2, c); 
}


void collect(current: (Expr) `<Expr e1> - <Expr e2>`, Collector c){
    collect(e1, e2, c);
    collectInfixOperation(current, "-", infixArithmetic, e1, e2, c); 
}

void collect(current: (Expr) `<Expr e1> * <Expr e2>`, Collector c){
    collect(e1, e2, c);
    collectInfixOperation(current, "*", infixArithmetic, e1, e2, c); 
}

void collectInfixOperation(Tree current, str op, AType (AType,AType) infixFun, Tree lhs, Tree rhs, Collector c) {
	c.calculate("<op>",current, [lhs, rhs], AType(Solver s) {
		try
			return infixFun(s.getType(lhs), s.getType(rhs));
		catch str msg:{
			println(msg);
			s.report(error(current, msg));
		}
		
	});
}

void customRequirement(uo:(UnaryOperator) `==`, AType t1, AType t2, Solver s) = {
	s.requireTrue(isAssignableToInteger(t2) , error(uo, "Both expressions must be convertible to integers"));
}
when isAssignableToInteger(t1);

void customRequirement(uo:(UnaryOperator) `==`, AType t1, AType t2, Solver s) = {
	s.requireEqual(t1,t2, error(uo, "Operands must have the same type"));
}
when !isAssignableToInteger(t1);	 

void customRequirement(UnaryOperator uo, AType t1, AType t2, Solver s) = {
		s.requireTrue(isAssignableToInteger(t1), error(uo, "Comparator operands must act upon integers"));
		s.requireTrue(isAssignableToInteger(t2), error(uo, "Comparator operands must act upon integers"));
	}
	when (UnaryOperator) `\>` := uo || (UnaryOperator) `\>=` := uo || (UnaryOperator) `\<` := uo || (UnaryOperator) `\<=` := uo;

	

// ----  Examples & Tests --------------------------------
TModel danTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config=getDanConfig(), debug=debug);
}

tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(refType(str name)) = <true, name, {structId()}>;
tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(AType t) = <false, "", {}>;

AType getTypeInAnonymousStruct(AType containerType, Tree selector, loc scope, Solver s){
    if(anonType(fields) :=  containerType){
    	return Set::getOneFrom((ListRelation::index(fields))["<selector>"]);
    }else{
    	s.report(error(selector, "Undefined field %q on %t", selector, containerType));
    }
}

private TypePalConfig getDanConfig() = tconfig(
    isSubType = isConvertible,
    getTypeNameAndRole = danGetTypeNameAndRole,
    getTypeInNamelessType = getTypeInAnonymousStruct,
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

