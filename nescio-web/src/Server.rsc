module Server

import util::Webserver;
import String;
import IO;
import Exception;

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

Response handle(r:post("/check", srcRequest)) {
    if (str src := srcRequest(#str)) {
        try {
            return jsonResponse(ok(), (), ("errors": [
                toRange(at) + ("message" :  msg)
                | error(msg, at) <- getMessages(getModel(src))
            ]));
        }
        catch ParseError(loc l) : 
            return jsonResponse(ok(), (), ("errors": [
                toRange(l[end = l.end[line = l.end.line + 1]][begin = l.begin[line = l.begin.line + 1]]) + ("message" : "Parse error")
            ]));
    }
    return response("{}");
}

default Response handle(Request r) = response(badRequest(), "Do not know how to handle: <r>");

@memo
TModel getModel(str source) = danTModelFromTree(parse(#start[Program], source, |project://fakeproject/|));

rel[loc use, loc def] getUseDefs(str source) = getUseDef(getModel(source));

Response lookup(str source, int line, int column) {
    for (<u, d> <- getUseDefs(source)) {
        if (u.begin.line == line && u.end.line == line && u.begin.column <= column && u.end.column >= column) {
            return jsonResponse(ok(), (), toRange(d));
        }
    }
    return response("{}");
}


map[str,map[str,int]] toRange(loc l) 
    = (
        "begin": ("line": l.begin.line, "column" : l.begin.column + 1),
        "end": ("line": l.end.line, "column" : l.end.column + 1)
    );
