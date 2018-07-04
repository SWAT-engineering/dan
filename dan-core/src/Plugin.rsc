module Plugin

import lang::dan::Syntax;
import lang::dan::Checker;
import lang::dan::Generator;
import ParseTree;

import IO;
import util::IDE;

import util::Reflective;
import lang::manifest::IO;

private str LANG_NAME = "DAN";

Contribution commonSyntaxProperties 
    = syntaxProperties(
        fences = {<"{","}">,<"(",")">}, 
        lineComment = "//", 
        blockComment = <"/*","*","*/">
    );
    
Tree checkDan(Tree input){
    model = danTModelFromTree(input); // your function that collects & solves
    types = getFacts(model);
  
  return input[@messages={*getMessages(model)}]
              [@hyperlinks=getUseDef(model)]
              [@docs=(l:"<prettyPrintAType(types[l])>" | l <- types)]
         ; 
}

Contribution compiler = builder(set[Message] (Tree tree) {
	  if (start[Program] prog := tree) {
        loc l = prog@\loc.top;
        l.extension = "java";
        newLoc =  |project://dan-core/dan-output/engineering/swat/formats/<l.file>|;
        newprog = compileDan(prog);
        writeFile(newLoc, newprog);
        return {};
      }
      return {error("Not a <LANG_NAME> program", tree@\loc)};
   });
 

void main() {
	registerLanguage(LANG_NAME, "dan", start[Program](str src, loc org) {
		return parse(#start[Program], src, org);
 	});
	
	registerContributions(LANG_NAME, {
        commonSyntaxProperties,
        compiler,
        treeProperties(hasQuickFixes = false), // performance
        annotator(checkDan)
    });
}