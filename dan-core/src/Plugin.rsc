module Plugin

import lang::dan::Syntax;
import lang::dan::Checker;
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

void main() {
	registerLanguage(LANG_NAME, "dan", start[Program](str src, loc org) {
		return parse(#start[Program], src, org);
 	});

	registerContributions(LANG_NAME, {
        commonSyntaxProperties,
        treeProperties(hasQuickFixes = false), // performance
        annotator(checkDan)
    });
}