module Server

import util::Webserver;
import String;


void main(int port) {
    serve(|http://localhost:<"<port>">|, Response (Request r) {
        if (get(str path) := r) {
            if (startsWith(path, "/lib/")) {
                return response(|project://nescio-web/node_modules/<path[5..]>|);
            }
            if (path == "/") {
                return response(|project://nescio-web/src/index.html|);
            }
            if (startsWith(path, "/def/")) {
                // handle definition lookup
                return handleDefinition(r);
            }
        }
        return response(badRequest(), "Do not know how to handle: <r>");
    });
}

void restart(int port) {
    shutdown(|http://localhost:<"<port>">|);
    main(port);
}

Response handleDefinition(Request r) {
    return response("TODO");
}