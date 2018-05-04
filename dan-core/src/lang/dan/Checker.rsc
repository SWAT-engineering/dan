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
	| anonTy(lrel[str, AType] fields)
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
    ;
    	
bool isSubType(AType _, topTy()) = true;
bool isSubType(tokenTy(_), tokenTy("Token")) = true;
bool isSubType(AType t1, AType t2) = true
	when t1 == t2;
default bool isSubType(AType _, AType _) = false;

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

void collect(current: (Program) `<TopLevelDecl* decls>`, TBuilder tb){
    tb.enterScope(current);
        collect(decls, tb);
    tb.leaveScope(current);
}
 
void collect(current:(TopLevelDecl) `struct <Id id> <Formals? formals> <Annos? annos> { <DeclInStruct* decls> }`,  TBuilder tb) {
     tb.define("<id>", structId(), id, defType(tokenTy(refTy("<id>"))));
     structScope = tb.getScope(); 
     tb.enterScope(current); {
        collect(decls, tb);
    }
    tb.leaveScope(current);
}


void collect(current:(DeclInStruct) `<Type ty> <Id id> = <Expr expr>`,  TBuilder tb) {
	tb.define("<id>", fieldId(), id, defType(transType(ty)));
	collect(expr, tb);
	tb.require("good_assignment", current, [expr],
        () { subtype(getType(expr), transType(ty)) || reportError(expr, "Expression sould be `<ty>`, found <fmt(expr)>"); });
}     

void collect(current: (Expr) `<StringLiteral lit>`, TBuilder tb){
    tb.fact(current, basicTy(string()));
}

void collect(current: (Expr) `<NatLiteral nat>`, TBuilder tb){
    tb.fact(current, basicTy(integer()));
}

// ----  Examples & Tests --------------------------------
private TypePalConfig getDanConfig() = tconfig(
    isSubType = isSubType
);

public Program sampleDan(str name) = parse(#Program, |project://dan-core/examples/<name>.dan|);
                     
list[Message] validateDan(str name) {
    Tree pt = sampleDan(name);
    tb = newTBuilder(pt, config = getDanConfig());
    collect(pt, tb);
    tm = tb.build();
    tm = validate(tm, isSubType=isSubType);
    return tm.messages;
}
 value main() = validateDan("e1");
