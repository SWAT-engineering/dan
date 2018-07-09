module Server

import util::Webserver;
import String;
import IO;

import lang::dan::Syntax;
import lang::dan::Checker;
import ParseTree;
import util::Reflective;

void main(int port) {
    serve(|http://localhost:<"<port>">|, handle);
}

void restart(int port) {
    shutdown(|http://localhost:<"<port>">|);
    main(port);
}

Response handle(get("/")) = response(|project://nescio-web/src/index.html|);
Response handle(get(/^\/lib\/<rest:.*>$/)) = response(|project://nescio-web/node_modules/| + rest);
Response handle(r:post("/def", srcRequest)) {
    if (str src := srcRequest(#str)) {
        return lookup(src, toInt(r.parameters["line"]), toInt(r.parameters["col"]) - 1);
    }
    return response("{}");
}

default Response handle(Request r) = response(badRequest(), "Do not know how to handle: <r>");

@memo
rel[loc use, loc def] getUseDefs(str source) = getUseDef(danTModelFromTree(parse(#start[Program], source, |project://fakeproject/|)));

Response lookup(str source, int line, int column) {
    for (<u, d> <- getUseDefs(source)) {
        if (u.begin.line == line && u.end.line == line && u.begin.column <= column && u.end.column >= column) {
            return jsonResponse(ok(), (), (
                "begin": ("line":d.begin.line, "column" : d.begin.column + 1),
                "end": ("line":d.end.line, "column" : d.end.column + 1)
                ));
        }
    }
    return response("{}");
}