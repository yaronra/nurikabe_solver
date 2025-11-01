from flask import Flask, render_template, request, jsonify, Response, stream_with_context
import requests
import queue, threading, traceback, json

from solver_adapter import solve_nurikabe
import progress

app = Flask(__name__, static_folder="static", template_folder="templates")


@app.route("/", methods=["GET"])
def index():
    """Serve the single‑page UI."""
    return render_template("index.html")


@app.route("/api/solve", methods=["POST"])
def api_solve():
    """
    Accept JSON:
        { "rows": 5, "cols": 5,
          "clues": [[null, null, 2, null, null], ...] }
    Return JSON:
        { "status": "ok",  "solution": [[0,1,1,0,0] ...] }
        { "status": "unsat", "message": "No solution" }
        { "status": "error", "message": "...trace..." }
    """
    try:
        data = request.get_json(force=True)
        rows, cols = data["rows"], data["cols"]
        clues = data["clues"]          # List of lists; None for empty cells

        solution = solve_nurikabe(rows, cols, clues)
        if isinstance(solution, str):
            return jsonify(status="unsat",
                           message=solution), 200

        return jsonify(status="ok", solution=solution), 200

    except Exception as exc:
        tb = traceback.format_exc()
        return jsonify(status="error",
                       message=str(exc) + str(tb),
                       traceback=tb), 500


@app.route("/api/solve_stream", methods=["POST"])
def api_solve_stream():
    """
    POST  {rows, cols, clues}
    SSE   partial → [board],  ok → final board,  unsat/error → msg
    """
    data  = request.get_json(force=True)
    rows, cols, clues = data["rows"], data["cols"], data["clues"]

    q = queue.Queue()

    # --- spawn solver in a worker thread ----------------------
    def run():
        progress.bind(q)
        try:
            final = solve_nurikabe(rows, cols, clues)   # unchanged API
            q.put(("DONE", final))                      # if unsolved, message string replaces board
        except Exception:
            q.put(("ERR", traceback.format_exc()))
        finally:
            progress.unbind()

    threading.Thread(target=run, daemon=True).start()
    # ----------------------------------------------------------

    def event_stream():
        hdr = lambda d: f"data: {json.dumps(d, separators=(',',':'))}\n\n"
        while True:
            msg = q.get()
            tag, payload = msg if isinstance(msg, tuple) else ("PART", msg)
            if tag == "PART":
                yield hdr({"status": "partial", "solution": payload})
            elif tag == "DONE":
                if isinstance(payload, str):
                    yield hdr({"status": "unsat", "message": payload})
                else:
                    yield hdr({"status": "ok"})
                break
            elif tag == "ERR":
                yield hdr({"status": "error", "message": payload})
                break

    return Response(stream_with_context(event_stream()),
                    mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache"})


# ------------------ NEW: Janko loader endpoint --------------------
@app.route("/api/janko/fetch", methods=["POST"])
def api_janko_fetch():
    """
    Body: { "id": "768" }
    Returns: { status:"ok", rows:int, cols:int, clues:[[int|None,...],...], source:url }
             or { status:"error", message:str }
    """
    try:
        data = request.get_json(force=True)
        raw_id = str(data.get("id", "")).strip()
        if not raw_id.isdigit():
            return jsonify(status="error", message="ID must be numeric."), 400
        n = int(raw_id)
        if not (1 <= n <= 9999):
            return jsonify(status="error", message="ID out of range 1..9999."), 400

        try:
            id4 = f"{n:04d}"
            url = f"https://www.janko.at/Raetsel/Nurikabe/{id4}.a.htm"
            html = _http_get(url)
            lines = html.split('\n')
            i_problem = lines.index('[problem]')
            i_solution = lines.index('[solution]')
            grid = [_parse_line(lines[i]) for i in range(i_problem+1, i_solution)]
        except:
            return jsonify(status="error",
                           message="Could not parse puzzle from page."), 502

        rows, cols = len(grid), len(grid[0]) if grid else (0, 0)
        return jsonify(status="ok", rows=rows, cols=cols, clues=grid, source=url)
    except Exception as exc:
        return jsonify(status="error", message=str(exc)), 500

def _http_get(url: str) -> str:
    headers = {"User-Agent": "Nurikabe-Loader/1.0"}
    r = requests.get(url, headers=headers, timeout=15)
    r.raise_for_status()
    return r.text

def _parse_line(line):
    return [None if item == '-' else int(item) for item in line.split()]

if __name__ == "__main__":
    # Development server – do *not* use in production
    app.run(debug=True, port=5000)


