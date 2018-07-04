module lang::dan::Generator

import IO;

import lang::dan::Syntax;
import lang::dan::Checker;
import analysis::graphs::Graph;


import List;
import Set;

extend analysis::typepal::TypePal;

syntax Aux = "{" SideCondition? sc "}";

int BYTE_SIZE = 8;

bool isSimpleByteType(uType(_)) = true;
bool isSimpleByteType(sType(_)) = true;
bool isSimpleByteType(AType _) = false;

int sizeSimpleByteType(uType(n)) = n;
int sizeSimpleByteType(sType(n)) = n;  
int sizeSimpleByteType(AType ty){ throw "Incorrect operation on type <prettyPrintAType(ty)>"; }

str calculateEq({intType()}) = "eqNum";
str calculateEq({strType()}) = "eqStr";
str calculateEq({strType(), uType(_)}) =  "eq";
str calculateEq({strType(), sType(_)}) = "eq";
str calculateEq({intType(), uType(_)}) = "eq";
str calculateEq({intType(), sType(_)}) = "eq";	
str calculateEq({sType(_)}) = "eq";
str calculateEq({uType(_)}) = "eq";
str calculateEq({uType(_), listType(intType())}) = "eq";

//default str calculateEq(set[AType] ts) { throw "Incorrect arguments to calculateEq: <ts>"; }

bool biprintln(value v){
	iprintln(v);
	return true;
} 

str makeSafeId(str id, loc lo) =
	"<newId>_<lo.offset>_<lo.length>_<lo.begin.line>_<lo.end.line>_<lo.begin.column>_<lo.end.column>"
	when newId := (("<id>"=="_")?"dummy":"<id>");

str compile(current: (Program) `module <Id moduleName> <Import* imports> <TopLevelDecl* decls>`, rel[loc,loc] useDefs, map[loc, AType] types)
	= "package engineering.swat.formats;
      '
      'import io.parsingdata.metal.token.Token;
	  '
	  'import static io.parsingdata.metal.token.Token.EMPTY_NAME;
	  'import static io.parsingdata.metal.Shorthand.*;
	  '
	  'public class <safeId> {
	  '\tprivate <safeId>(){}
	  '\t<intercalate("\n", [compile(d, useDefs, types, index) | d <- decls])>
	  '}"
	when safeId := moduleName, //makeSafeId("<moduleName>", current@\loc),
		 map[loc, TopLevelDecl] declsMap := (d@\loc: d | d <- decls),
		 list[loc] tmpLos := [lo | lo <- order(useDefs), lo in declsMap],
		 set[loc] los :=  domain(declsMap) - toSet(tmpLos),
		 bprintln(intercalate("\n", tmpLos)),
		 Tree(loc) index := Tree(loc l){
		 	visit (current){
		 		case Tree t: {
		 			if (t has \loc){
		 				if (l == t@\loc){
		 				 	return t;
		 				}
		 			}
		 		}
		 	};
		 	throw "no corresponding tree has been found for location <l>";
		 };
		 
str compile(current:(TopLevelDecl) `choice <Id id> <Formals? formals> <Annos? annos> { <DeclInChoice* decls> }`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
   "public static final Token <safeId><compiledFormals> <startBlock> <compiledDecls>; <endBlock>"
   when safeId := makeSafeId("<id>", current@\loc),
		 areThereFormals := (fls <- formals),
		 startBlock := (areThereFormals?"{ return ":"="),
		 endBlock := (areThereFormals?"}":""),
		 compiledFormals := {if (fs  <- formals) compile(fs, useDefs, types, index); else "";},
		 declsNumber := (0| it +1 | d <-decls),
		 compiledDecls := ((declsNumber == 0)?"EMPTY":
		 	((declsNumber ==  1)? (([compile(d,useDefs,types, index) | d <-decls])[0]) : "cho(<intercalate(", ", ["\"<safeId>\""] + [compile(d, useDefs, types, index) | d <-decls])>)"))
		 ; 		 
 
str compile(current:(TopLevelDecl) `struct <Id id> <Formals? formals> <Annos? annos> { <DeclInStruct* decls> }`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
   "public static final Token <safeId><compiledFormals> <startBlock> <compiledDecls>; <endBlock>"           	
	when safeId := makeSafeId("<id>", current@\loc),
		 areThereFormals := (fls <- formals),
		 startBlock := (areThereFormals?"{ return ":"="),
		 endBlock := (areThereFormals?"}":""),
		 compiledFormals := {if (fs  <- formals) compile(fs, useDefs, types, index); else "";},
		 declsNumber := (0| it +1 | d <-decls),
		 compiledDecls := ((declsNumber == 0)?"EMPTY":
		 	((declsNumber ==  1)? (([compile(d,useDefs,types, index) | d <-decls])[0]) : "seq(<intercalate(", ", ["\"<safeId>\""] + [compile(d, useDefs, types, index) | d <-decls])>)"))
		 ;

str compile(current:(DeclInStruct) `<Type ty>[] <DId id> <Arguments? args> <SideCondition? cond>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	"rep(\"<safeId>\", <compile(current, ty, id, args, cond, useDefs, types, index)>)"
	when safeId := makeSafeId("<id>", id@\loc)
		;
		
str compile(current:(DeclInStruct) `<Type ty>[] <DId id> <Arguments? args> [<Expr n>] <SideCondition? cond>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	{if (aCond <- cond)
		"def(\"<safeId>\", mul(con(<size/8>), <compile(n, useDefs, types, index)>), <compileSideCondition(aCond, aty, useDefs, types, index)>)";
	else
		"def(\"<safeId>\", mul(con(<size/8>), <compile(n, useDefs, types, index)>))";}
	when safeId := makeSafeId("<id>", id@\loc),
		 AType aty := types[ty@\loc],
		 isSimpleByteType(aty),
		 int size := sizeSimpleByteType(aty);
		
		 
str compile(current:(DeclInStruct) `<Type ty>[] <DId id> <Arguments? args> [<Expr n>] <SideCondition? cond>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	{if (aCond <- cond)
		"post(repn(\"<safeId>\", <compile(current, ty, id, args, emptyCond, useDefs, types, index)>,  <compile(n, useDefs, types, index)>), <compile(aCond, useDefs, types, index)>)";
	else
		"repn(\"<safeId>\", <compile(current, ty, id, args, emptyCond, useDefs, types, index)>,  <compile(n, useDefs, types, index)>)";}
	when emptyCond := ([Aux] "{ }").sc,
		 safeId := makeSafeId("<id>_ARR", current@\loc),
		 aty := types[ty@\loc],
		 !isSimpleByteType(aty);
		 
str compile(DeclInStruct current, Type ty, DId id, Arguments? args, SideCondition? cond, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	=  compileType(ty, safeId, compiledArgs, compiledCond, useDefs, types, index)
	when safeId := makeSafeId("<id>", id@\loc),
		 AType aty := types[ty@\loc],
		 compiledArgs := ("" | it + compile(aargs, useDefs, types, index) | aargs <- args),
		 compiledCond := ("" | it + ", <compileSideCondition(c, aty, useDefs, types, index)>" | c <- cond);   
	        	
str compile(current:(DeclInStruct) `<Type ty> <DId id> <Arguments? args> <Size? size> <SideCondition? cond>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	compile(current, ty, id, args, cond, useDefs, types, index);
		 
str compile(current:(DeclInChoice) `<Type ty>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	compileForChoice(ty, useDefs, types, index);
	
str compileForChoice((Type) `struct { <DeclInStruct* decls>}`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	compiledDecls           	
	when declsNumber := (0| it +1 | d <-decls),
		 compiledDecls := ((declsNumber == 0)?"EMPTY":
		 	((declsNumber ==  1)? (([compile(d,useDefs,types,index) | d <-decls])[0]) : "seq(<intercalate(", ", ["\"<safeId>\""] + [compile(d, useDefs, types, index) | d <-decls])>)"))
		 ;

str compileForChoice(current:(Type) `<Id typeId>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	compile(current, useDefs, types, index);

		 
str compileSideCondition((SideCondition) `?(== <Expr e>)`, AType t1, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	calculateOp("==", {t1,t2}, [compile(e, useDefs, types, index)])
	when t2 := types[e@\loc];

str compileSideCondition((SideCondition) `?(!= <Expr e>)`, AType t1,  rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	calculateOp("!=", {t1,t2}, [compile(e, useDefs, types, index)])
	when t2 := types[e@\loc];
	
str calculateOp("==", set[AType] ts, list[str] es) = "<calculateEq(ts)>(<intercalate(",", es)>)";
str calculateOp("!=", set[AType] ts, list[str] es) = "not(<calculateEq(ts)>(<intercalate(",", es)>))";
str calculateOp("&&", set[AType] ts, list[str] es) = "and(<intercalate(",", es)>)";
str calculateOp("||", set[AType] ts, list[str] es) = "or(<intercalate(",", es)>)";
str calculateOp("\>", set[AType] ts, list[str] es) = "gtNum(<intercalate(",", es)>)";
str calculateOp("\<", set[AType] ts, list[str] es) = "ltNum(<intercalate(",", es)>)";
str calculateOp("\>=", set[AType] ts, list[str] es) = "gtEqNum(<intercalate(",", es)>)";
str calculateOp("\<=", set[AType] ts, list[str] es) = "ltEqNum(<intercalate(",", es)>)";
	

default str calculateOp(str other, set[AType] ts){ throw "generation for operator <other> not yet implemented"; }

default str compileSideCondition(current:(SideCondition) `? ( <Expr e>)`, AType ty, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	= compile(e, useDefs, types, index);
	
default str compileSideCondition(SideCondition sc, AType ty, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index){ throw "Not yet implemented: <sc>"; } 

str compile(Formals current, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	= "(<intercalate(", ", actualFormals)>)"
	when actualFormals := [compile(af, useDefs, types, index) | af <- current.formals];
	
str compile(current:(Formal) `<Type ty> <Id id>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	= "ValueExpression <safeId>" 
	when safeId := makeSafeId("<id>", current@\loc);

		 
str compile((Arguments)  `( <{Expr ","}* args>  )`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	= "(<intercalate(", ", actualArgs)>)"
	when actualArgs := [compile(arg, useDefs, types, index) | arg <- args];	 

str compileType(current:(Type)`<UInt v>`, str containerId, str args, str cond, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	(cond == "")? "def(\"<containerId>\", con(<toInt("<v>"[1..])/BYTE_SIZE>))" : "def(\"<containerId>\", con(<toInt("<v>"[1..])/BYTE_SIZE>) <cond>)";	

str compileType(current:(Type)`<Id id>`, str containerId, str args, str cond, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	(args? == "")?safeId:"<safeId><args>"
	when lo := ([l | l <- useDefs[id@\loc]])[0],
		 safeId := makeSafeId("<id>", lo);
	

	
str compile(current:(Type)`<UInt v>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	"nod(<toInt("<v>"[1..])/BYTE_SIZE>)";

str compile(current:(Type)`<Id id>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	makeSafeId("<id>", lo)
	when lo := ([l | l <- useDefs[id@\loc]])[0];
	

str compile(current:(SideCondition) `while ( <Expr e>)`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index){
	
}

str compile(current:(SideCondition) `? ( <ComparatorOperator uo> <Expr e>)`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	= compile(uo, compile(e, useDefs, types, index), useDefs, types, index);

default str compile(current:(SideCondition) `? ( <UnaryOperator uo> <Expr e>)`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index)
	= compile(uo, compile(e, useDefs, types, index), useDefs, types, index)
	;

str compile(current:(ComparatorOperator) `\>=`, str s, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "gtEqNum(<s>)";

str compile(current:(UnaryOperator) `==`, str s, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "eq(<s>)";

str compile(current:(UnaryOperator) `!=`, str s, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "not(eq(<s>))";

str compile(current: (Expr) `<Expr e>.as[<Type t>]`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = compile(e, useDefs, types, index);

str compile(current: (Expr) `<StringLiteral lit>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "con(<lit>)";

str compile(current: (Expr) `<HexIntegerLiteral nat>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "con(<nat>)";

str compile(current: (Expr) `<BitLiteral nat>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "";

str compile(current: (Expr) `<NatLiteral nat>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "con(<nat>)";

str compile(current: (Expr) `(<Expr e>)`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = compile(e, useDefs, types, index);

str compile(current: (Expr) `<Id id> ( <{Expr ","}* exprs>)`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
    "new <javaId>().apply(<intercalate(", ", [compile(e, useDefs, types, index) | Expr e <- exprs])>)"
    when loc funLoc := Set::getOneFrom((useDefs[id@\loc])),
    	 funType(_,_,_,javaId) := types[funLoc];

str compile(current: (Expr) `<Expr e1> - <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
    "<getInfixOperator("-")>(<compile(e1, useDefs, types, index)>, <compile(e2, useDefs, types, index)>)";
    
str compile(current: (Expr) `<Expr e1> + <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
    "<getInfixOperator("+")>(<compile(e1, useDefs, types, index)>, <compile(e2, useDefs, types, index)>)";    

str compile(current: (Expr) `<Expr e1> ++ <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
    "<getInfixOperator("++")>(<compile(e1, useDefs, types, index)>, <compile(e2, useDefs, types, index)>)";    

str getInfixOperator("-") = "sub";
str getInfixOperator("+") = "add";
str getInfixOperator("++") = "cat";

str compile(current: (Expr) `[ <{Expr ","}* es>]`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "con(<intercalate(", ",["<e>" | e <- es])>)"
	when listType(ty) := types[current@\loc]; 

str compile(current: (Expr) `<Id id>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) = "last(ref(\"<makeSafeId("<srcId>", lo)>\"))" 
	when lo := ([l | l <- useDefs[id@\loc]])[0],
		 srcId := "<index(lo)>";
		 
str compile(current: (Expr) `<Expr e1> <ComparatorOperator uo> <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	calculateOp("<uo>", {t1,t2}, [compile(e1, useDefs, types, index), compile(e2, useDefs, types, index)])
	when t1 := types[e1@\loc],
		 t2 := types[e2@\loc];
		 
str compile(current: (Expr) `<Expr e1> <EqualityOperator uo> <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	calculateOp("<uo>", {t1,t2}, [compile(e1, useDefs, types, index), compile(e2, useDefs, types, index)])
	when t1 := types[e1@\loc],
		 t2 := types[e2@\loc];
	
		 
		 
str compile(current: (Expr) `<Expr e1> && <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	calculateOp("&&", {t1,t2}, [compile(e1, useDefs, types, index), compile(e2, useDefs, types, index)])
	when t1 := types[e1@\loc],
		 t2 := types[e2@\loc];
		 
str compile(current: (Expr) `<Expr e1> || <Expr e2>`, rel[loc,loc] useDefs, map[loc, AType] types, Tree(loc) index) =
	calculateOp("||", {t1,t2}, [compile(e1, useDefs, types, index), compile(e2, useDefs, types, index)])
	when t1 := types[e1@\loc],
		 t2 := types[e2@\loc];
		 
str type2Java(AType t) = "ValueExpression"
	when isTokenType(t);	  
str type2Java(intType()) = "int";
str type2Java(strType()) = "String";
str type2Java(boolType()) = "boolean";
str type2Java(listType(t)) = "List\<<type2Java(t)>\>"
	when !isTokenType(t);	  
            	

public start[Program] sampleDan(str name) = parse(#start[Program], |project://dan-core/<name>.dan|);

str compileDan(str name) {
    start[Program] pt = sampleDan(name);
    TModel model = danTModelFromTree(pt);
    map[loc, AType] types = getFacts(model);
    rel[loc, loc] useDefs = getUseDef(model);
    return compile(pt.top, useDefs, types);
}

void compileDanTo(str name, loc file) {
    str text = compileDan(name);
    //println(text);
    writeFile(file, text);
}
