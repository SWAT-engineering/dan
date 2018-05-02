module Plugin

import lang::dan::Syntax;
import ParseTree;

import IO;
import util::IDE;

private str LANG_NAME = "DAN";


void main() {
  registerLanguage(LANG_NAME, "dan", start[Program](str src, loc org) {
    return parse(#start[Program], src, org);
  });

}