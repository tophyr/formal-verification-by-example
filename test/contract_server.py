"""Local HTTP server for test/curl-contract.sh. Responds with the status code
given as the request path (e.g. POST /500 -> 500) and records what it got."""
import http.server, sys

class H(http.server.BaseHTTPRequestHandler):
    def record(self, body):
        open(sys.argv[2] + ".body", "wb").write(body)
        open(sys.argv[2] + ".headers", "w").write(str(self.headers))

    def do_POST(self):
        self.record(self.rfile.read(int(self.headers.get("Content-Length", 0))))
        self.send_response(int(self.path.strip("/") or 200)); self.end_headers()
        self.wfile.write(b'{"id":"x"}\n')

    def do_GET(self):
        self.record(b"")
        self.send_response(int(self.path.strip("/") or 200)); self.end_headers()
        self.wfile.write(b"line1\nline2")

    def log_message(self, *a): pass

http.server.HTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
