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

// covariant lists
bool isConvertible(listType(t1), listType(t2)) = isConvertible(t1, t2);

bool isConvertible(AType t1, AType t2) = true
	when t1 == t2;
default bool isConvertible(AType _, AType _) = false;

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(boolType()) = "bool";
str prettyPrintAType(listType(t)) = "<prettyPrintAType(t)>[]";
str prettyPrintAType(refType(name)) = name;
str prettyPrintAType(anonType(_)) = "anonymous";
str prettyPrintAType(u8()) = "u8";
str prettyPrintAType(u16()) = "u16";
str prettyPrintAType(u32()) = "u32";
str prettyPrintAType(u64()) = "u64";
str prettyPrintAType(consType(formals)) = "constructor(<("" | it + "<prettyPrintAType(ty)>," | atypeList(fs) := formals, ty <- fs)>)";

bool isTokenType(u8()) = true;
bool isTokenType(u16()) = true;
bool isTokenType(u32()) = true;
bool isTokenType(u64()) = true;
bool isTokenType(refType(_)) = true;
bool isTokenType(anonType(_)) = true;
bool isTokenType(listType(t)) = isTokenType(t);
bool isTokenType(consType(_)) = true;  
default bool isTokenType(AType t) = false;

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


void collect(current: (Program) `<TopLevelDecl* decls>`, Collector c){
    c.enterScope(current);
    currentScope = c.getScope();
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
     	for (fs <- formals)
     		collectFormals(id, fs, c);
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
		s.requireTrue(isTokenType(s.getType(ty)), error(ty, "Non-initialized fields must be of a token type, but it was %t", ty));
	});
	if ("<id>" != "_"){
		c.define("<id>", fieldId(), id, defType(ty));
	}
	collect(ty, c);
	for (aargs <- args){
		collectArgs(ty, aargs, c);
	}
	for (sz <-size){
		collectSize(ty, sz, c);
	}
	for (sc <- cond){
		collectSideCondition(ty, sc, c);
	}
}

void collectSideCondition(Type ty, current:(SideCondition) `? ( <Expr e>)`, Collector c){
	collect(e, c);
	c.define("this", variableId(), current, defType(ty));
	c.require("side condition", current, [e], void (Solver s) {
		s.requireEqual(s.getType(e), boolType(), error(current, "Side condition must be boolean"));
	});
}

void collectSideCondition(Type _, current:(SideCondition) `? ( <UnaryOperator uo> <Expr e>)`, Collector c){
	collect(e, c);
	c.require("side condition", current, [e], void (Solver s) {
		s.requireSubtype(s.getType(e), intType(), error(current, "Expression in unary side condition must have numeric type"));
	});
	//c.requireEqual(ty, e, error(sc, "Unary expression in side condition must have the same type as declaration"));
}

void collectSize(Type ty, Size sz, Collector c){
	collect(sz.expr, c);
	c.require("size argument", sz, [ty] + [sz.expr], void (Solver s) {
		s.requireTrue(s.getType(ty) is listType, error(sz, "Setting size on a non-list element"));
		s.requireSubtype(s.getType(sz.expr), intType(), error(sz, "Size must be an integer"));
	});
}

void collectArgs(Type ty, Arguments current, Collector c){
		currentScope = c.getScope();
		for (a <- current.args)
			collect(a, c);
		c.require("constructor arguments", current, [ty] + [a | a <- current.args], void (Solver s) {
			s.requireTrue(refType(_) := s.getType(ty)  || listType(refType(_)) := s.getType(ty), error(current, "Constructor arguments only apply to user-defined types but got %t", ty));
			ty_ = top-down-break visit (ty){
				case (Type)`<Type t> []` => t
				case Type t => t
			};
			tyLoc = ty@\loc;
			conId = fixLocation(parse(#Type, "<ty_>"), tyLoc[offset=tyLoc.offset + tyLoc.length]);
			ct = s.getTypeInType(s.getType(ty_), conId, {consId()}, currentScope);
			argTypes = atypeList([ s.getType(a) | a <- current.args ]);
			s.requireSubtype(ct.formals, argTypes, error(current, "Wrong type of arguments"));
		});
	
}

void collectFormals(Id id, Formals current, Collector c){
	actualFormals = [af | af <- current.formals];
	c.define("<id>", consId(), id, defType(actualFormals, AType(Solver s) {
     		return consType(atypeList([s.getType(a) | a <- actualFormals]));
    }));
    collect(actualFormals, c);
}

void collect(current:(TopLevelDecl) `choice <Id id> <Formals? formals> <Annos? annos> { <DeclInChoice* decls> }`,  Collector c) {
	 // TODO  explore `Solver.getAllDefinedInType` for implementing the check of abstract fields
	 c.define("<id>", structId(), current, defType(refType("<id>")));
     c.enterScope(current); {
     	for (fs <- formals)
     		collectFormals(id, fs, c);
     	collect(decls, c);
     	ts = for (d <- decls){
     			switch (d){
     				case (DeclInChoice) `abstract <Type ty> <Id _>`: append(ty);
     				case (DeclInChoice) `<Type ty> <Arguments? _> <Size? _>`: append(ty);
     			};
     		};
     	currentScope = c.getScope();
     	c.require("abstract fields", current, [id] + ts, void(Solver s){
     		//ts = for ((DeclInChoice) `<Type ty> <Arguments? args> <Size? size>` <- decls){
     		//	append(s.getType(ty));
     		//};
     		rel[str id,AType ty] abstractFields = s.getAllDefinedInType(refType("<id>"), currentScope, {fieldId()});
     		for (actualFormals <- formals, formal <- actualFormals.formals)
     			abstractFields = {f | f <-abstractFields, f.id != "<formal.id>"};
     		 for ((DeclInChoice) `<Type ty> <Arguments? args> <Size? size>` <- decls){
     			//set[str id, AType ty] fsConcrete = //s.getAllDefinedInType(s.getType(ty), currentScope, {fieldId()});
     			for (f <- abstractFields){
     				try{
     					AType t = s.getTypeInType(s.getType(ty), [Id] "<f.id>", { fieldId() }, currentScope);
     				}catch _:{
     					s.report(error(ty, "Missing implementation of abstract field")); 
     				};
     				
     			};
     			
     		};
     			
     	});
    }
    c.leaveScope(current);
    
}

void collect(current:(DeclInChoice) `abstract <Type ty> <Id id>`,  Collector c) {
	c.define("<id>", fieldId(), id, defType(ty));
	collect(ty, c);
}

void collect(current:(DeclInChoice) `<Type ty> <Arguments? args> <Size? size>`,  Collector c) {
	c.require("declared type", ty, [ty], void(Solver s){
		s.requireTrue(isTokenType(s.getType(ty)), error(ty, "Non-initialized fields must be of a token type but it was %t", ty));
	});
	collect(ty, c);
	for (aargs <- args){
		// TODO check if it works to pass ty as second argument, i.e.,
		// parent node of new artificially created node
		collectArgs(ty, aargs, c);
	}
	for (sz <-size){
		collectSize(ty, sz, c);
	}
}

void collect(current:(UnaryExpr) `<UnaryOperator uo> <Expr e>`, Collector c){
	collect(e, c);
}


void collect(current:(Type)`u8`, Collector c) {
	c.fact(current, u8());
}

void collect(current:(Type)`u16`, Collector c) {
	c.fact(current, u16());
}

void collect(current:(Type)`u32`, Collector c) {
	c.fact(current, u32());
}

void collect(current:(Type)`u64`, Collector c) {
	c.fact(current, u64());
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
	fields =for (d <-decls){
			switch(d){
				case (DeclInStruct) `<Type t> <Id id> = <Expr e>`: append(<"<id>", t>);
				case (DeclInStruct) `<Type t> <DId id> <Arguments? args> <Size? size> <SideCondition? sc>`: append(<"<id>", t>);
			};
		};
	//for (<id, ty> <- fields){
	//		c.define("<id>", fieldId(), current, defType(ty));
	//};
	c.calculate("anonymous struct type", current, [ty | <_, ty> <- fields], AType(Solver s){
		return anonType([<id, s.getType(ty)> | <id, ty> <- fields]);
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

void collect(current: (Expr) `<Expr e>[<Range r>]`, Collector c){
	collect(e, c);
	c.require("list expression", current, [e], void(Solver s){
			s.requireTrue(listType(_) := s.getType(e), error(e, "Expression must be of list type"));
		});
	collectRange(current, e, r, c);
}

void collectRange(Expr access, Expr e, current:(Range) `: <Expr end>`, Collector c){
	collect(end, c);
	c.calculate("list access", access, [e, end], AType (Solver s){
		s.requireEqual(end, intType(), error(end, "Index must be integer"));
		return s.getType(e);
	});
}

void collectRange(Expr access, Expr e, current:(Range) `<Expr begin> : <Expr end>`, Collector c){
	collect(begin, end, c);
	c.calculate("list access", access, [e, begin, end], AType (Solver s){
		s.requireEqual(begin, intType(), error(begin, "Index must be integer"));
		s.requireEqual(end, intType(), error(end, "Index must be integer"));
		return s.getType(e);
	});
}

void collectRange(Expr access, Expr e, current: (Range) `<Expr begin> :`, Collector c){
	collect(begin, c);
	c.calculate("list access", access, [e, begin], AType (Solver s){
		s.requireEqual(begin, intType(), error(begin, "Index must be integer"));
		return s.getType(e);
	});
}
	
void collectRange(Expr access, Expr e, current: (Range) `<Expr idx>`, Collector c){
	collect(idx, c);
	c.calculate("list access", access, [e, idx], AType (Solver s){
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

void collect(current: (Expr) `(<Expr e>)`, Collector c){
    collect(e, c); 
}

void collectInfixOperation(Tree current, str op, AType (AType,AType) infixFun, Tree lhs, Tree rhs, Collector c) {
	c.calculate("<op>",current, [lhs, rhs], AType(Solver s) {
		try
			return infixFun(s.getType(lhs), s.getType(rhs));
		catch str msg:{
			s.report(error(current, msg));
		}
		
	});
}	

// ----  Examples & Tests --------------------------------
TModel danTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config=getDanConfig(), debug=debug);
}

tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(refType(str name)) = <true, name, {structId()}>;
tuple[bool isNamedType, str typeName, set[IdRole] idRoles] danGetTypeNameAndRole(AType t) = <false, "", {}>;

AType getTypeInAnonymousStruct(AType containerType, Tree selector, loc scope, Solver s){
    if(anonType(fields) :=  containerType){
    	return Set::getOneFrom((ListRelation::index(fields))["<selector>"]);
    } else if (consType(_) := containerType){
    	return containerType;	
    }
    else
    {	s.report(error(selector, "Undefined field <selector> on %t",containerType));
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

