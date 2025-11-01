const buildBtn = document.getElementById("buildBtn");
const solveBtn = document.getElementById("solveBtn");
const gridDiv  = document.getElementById("grid");
const spinner  = document.getElementById("spinner");
const statusLn = document.getElementById("status");
const gridWrap  = document.getElementById("gridWrap");
const jankoId   = document.getElementById("jankoId");
const loadBtn   = document.getElementById("loadJankoBtn");
const editBtn  = document.getElementById("editBtn");
const navBar    = document.getElementById("navBar");
const stepCtr   = document.getElementById("stepCounter");

let currentRows = 0, currentCols = 0;
let initialClues = [];             // keep numbers for later painting

// History of solutions
let snapshots = [];                 // array<board>
let stepIdx   = 0;                  // current index in snapshots
let solving   = false;

const prevBtn = document.getElementById("prevBtn");
const nextBtn = document.getElementById("nextBtn");

prevBtn.addEventListener("click", ()=> nav(-1));
nextBtn.addEventListener("click", ()=> nav(+1));
if (editBtn) editBtn.addEventListener("click", enterEditMode);
if (loadBtn) {
  loadBtn.addEventListener("click", loadFromJanko);
}
if (jankoId) {
  jankoId.addEventListener("keydown", (e) => {
    if (e.key === "Enter") loadFromJanko();
  });
}

// --- NEW: load a puzzle by ID from janko.at ---------------------
async function loadFromJanko() {
  const raw = (jankoId?.value || "").trim();
  if (!/^\d+$/.test(raw)) {
    statusLn.textContent = "Please enter a numeric Janko ID (e.g., 768).";
    statusLn.classList.remove("hidden");
    return;
  }
  const id = String(parseInt(raw, 10));   // normalize

  spinner.classList.remove("hidden");
  statusLn.textContent = `Loading puzzle #${id} from janko.at…`;
  statusLn.classList.remove("hidden");
  hideNav();

  try {
    const resp = await fetch("/api/janko/fetch", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ id })
    });
    const data = await resp.json();
    if (data.status !== "ok") {
      throw new Error(data.message || "Unable to load puzzle");
    }

    // set size inputs and rebuild input grid
    currentRows = data.rows;
    currentCols = data.cols;
    document.getElementById("rows").value = currentRows;
    document.getElementById("cols").value = currentCols;
    buildGrid();

    // pre-fill clues
    const inputs = gridDiv.querySelectorAll("input");
    for (let r = 0; r < currentRows; r++) {
      for (let c = 0; c < currentCols; c++) {
        const v = data.clues[r][c];
        if (v != null) {
          inputs[r * currentCols + c].value = v;
        }
      }
    }
    initialClues = data.clues.map(row => row.slice());

    solveBtn.disabled = false;
    editBtn?.classList.add("hidden");
    statusLn.textContent = `Loaded #${id} (${currentRows}×${currentCols}). Edit clues or click Solve!`;
  } catch (err) {
    statusLn.textContent = String(err);
  } finally {
    spinner.classList.add("hidden");
  }
}

document.addEventListener("keydown", e=>{
    if (!solving) {
        if (e.key === "ArrowLeft")  nav(-1);
        if (e.key === "ArrowRight") nav(+1);
    }
});

buildBtn.addEventListener("click", buildGrid);
solveBtn.addEventListener("click", sendToSolver);

function buildGrid() {
    currentRows = parseInt(document.getElementById("rows").value, 10);
    currentCols = parseInt(document.getElementById("cols").value, 10);
    if (currentRows < 2 || currentCols < 2) return;

    // Configure CSS grid columns
    gridDiv.style.gridTemplateColumns = `repeat(${currentCols}, 2.2rem)`;
    gridDiv.style.gridTemplateRows    = `repeat(${currentRows}, 2.2rem)`;
    gridDiv.innerHTML = "";  // clear previous

    for (let r = 0; r < currentRows; r++) {
        for (let c = 0; c < currentCols; c++) {
            const cell = document.createElement("div");
            cell.className = "cell";
            const inp = document.createElement("input");
            inp.type = "number";
            inp.min = "1";
            inp.addEventListener("click", e => e.stopPropagation());
            cell.appendChild(inp);
            gridDiv.appendChild(cell);
        }
    }
    gridDiv.classList.remove("hidden");
    solveBtn.disabled = false;
    statusLn.className = "hidden";

    // reset history
    snapshots = [];
    stepIdx   = 0;
    hideNav();
}

function sendToSolver() {
    const clues = [];
    const inputs = gridDiv.querySelectorAll("input");
    let hasAnyClue = false;
    for (let r = 0; r < currentRows; r++) {
        const row = [];
        for (let c = 0; c < currentCols; c++) {
            const val = inputs[r*currentCols + c].value;
            if (val !== "") hasAnyClue = true;
            row.push(val === "" ? null : parseInt(val, 10));
        }
        clues.push(row);
    }

    if (!hasAnyClue) {
        statusLn.textContent = "Enter at least one numeric clue before solving.";
        statusLn.classList.remove("hidden");
        return;
    }

    initialClues = clues.map(row => row.slice());   // deep copy

    spinner.classList.remove("hidden");
    statusLn.textContent = "Thinking...";
    statusLn.classList.remove("hidden");

    solving   = true;
    snapshots = [];
    solveBtn.disabled = true;           
    editBtn?.classList.add("hidden");  

const stream = fetch("/api/solve_stream", {
        method: "POST",
        headers: { "Content-Type": "application/json",
                   "Accept": "text/event-stream"},
        body: JSON.stringify({ rows: currentRows, cols: currentCols, clues })
    }).then(resp => consumeSSE(resp));
}

function showResult(data) {
    if (data.status === "ok") {
        paintSolution(data.solution);
        statusLn.textContent = "Solved!";
    } else {
        displayError(data.message || "Unknown failure");
    }
}

async function consumeSSE(resp) {
    const reader  = resp.body.getReader();
    const decoder = new TextDecoder();
    let buffer = "";
    while (true) {
        const { value, done } = await reader.read();
        if (done) break;
        buffer += decoder.decode(value, { stream: true });
        let idx;
        while ((idx = buffer.indexOf("\n\n")) >= 0) {
            const chunk = buffer.slice(0, idx).trim();
            buffer = buffer.slice(idx + 2);
            if (!chunk.startsWith("data:")) continue;
            const json = JSON.parse(chunk.slice(5));
            handleServerEvent(json);
        }
    }
}

function enterEditMode() {
    // Rebuild the grid as inputs, prefilled with original clues
    gridDiv.style.gridTemplateColumns = `repeat(${currentCols}, 2.2rem)`;
    gridDiv.innerHTML = "";
    for (let r = 0; r < currentRows; r++) {
        for (let c = 0; c < currentCols; c++) {
            const cell = document.createElement("div");
            cell.className = "cell";
            const inp = document.createElement("input");
            inp.type = "number";
            inp.min = "1";
            const clue = (initialClues && initialClues[r]) ? initialClues[r][c] : null;
            if (clue != null) inp.value = clue;
            cell.appendChild(inp);
            gridDiv.appendChild(cell);
        }
    }
    // Reset UI state for editing
    hideNav();                       // keep timeline hidden while editing
    spinner.classList.add("hidden");
    statusLn.textContent = "Edit the clues, then click Solve!";
    statusLn.classList.remove("hidden");
    solveBtn.disabled = false;
}

function handleServerEvent(msg) {
    if (msg.status === "partial") {
        snapshots.push(msg.solution);
        stepIdx = snapshots.length - 1;
        paintSolution(msg.solution);
        statusLn.textContent = `Thinking… (step ${snapshots.length})`;
    }
    else if (msg.status === "ok") {
        solving = false;
        statusLn.textContent = `Solved in ${snapshots.length} steps`;
        showNav();
        spinner.classList.add("hidden");
        solveBtn.disabled = false;
        if (editBtn) editBtn.classList.remove("hidden");
    }
    else if (msg.status === "unsat") {
        solving = false;
        statusLn.textContent = msg.message;
        showNav();
        spinner.classList.add("hidden");
        solveBtn.disabled = false;   
        if (editBtn) editBtn.classList.remove("hidden");
    }
    else if (msg.status === "error") {
        solving = false;
        spinner.classList.add("hidden");
        displayError(msg.message || "Internal error");
        solveBtn.disabled = false;
        if (editBtn) editBtn.classList.remove("hidden");
    }
}

function nav(delta) {
    if (snapshots.length === 0) return;
    stepIdx = (stepIdx + delta + snapshots.length) % snapshots.length;
    paintSolution(snapshots[stepIdx]);
    updateStepCounter();
}

function hideNav() {
    prevBtn.classList.add("hidden");
    nextBtn.classList.add("hidden");
}
function showNav() {
    if (snapshots.length > 1) {
        prevBtn.classList.remove("hidden");
        nextBtn.classList.remove("hidden");
    }
}

function hideNav()  { navBar.classList.add("hidden"); }
function showNav()  {
    if (snapshots.length > 1) {
        navBar.classList.remove("hidden");
        updateStepCounter();
    }
}

function updateStepCounter() {
    stepCtr.textContent = `Step ${stepIdx + 1} / ${snapshots.length}`;
}

function paintSolution(sol) {
    const cells = gridDiv.querySelectorAll(".cell");
    for (let r = 0; r < currentRows; r++) {
        for (let c = 0; c < currentCols; c++) {
            const idx = r*currentCols + c;
            const cell = cells[idx];
            cell.classList.remove("wall", "isle");
            cell.innerHTML = "";            // wipe any input/old text

            const clue = initialClues[r][c];
            if (sol[r][c] === 1) {          // sea
                cell.classList.add("wall");
            } else if (sol[r][c] === 0) {   // island
                cell.classList.add("isle");
                cell.textContent = clue != null ? clue : "●";
            } else {                        // unknown (-1)
                // leave blank white
                if (clue != null) cell.textContent = clue;
            }        
        }
    }
}

function displayError(msg) {
    statusLn.textContent = msg;
    statusLn.classList.remove("hidden");
}

enableDragScroll(gridWrap);

function enableDragScroll(el) {
    if (!el) return;
    let isDown = false, startX = 0, startY = 0, sx = 0, sy = 0, pid = null;
    el.addEventListener("pointerdown", (e) => {
        isDown = true;
        pid = e.pointerId;
        el.setPointerCapture(pid);
        startX = e.clientX;
        startY = e.clientY;
        sx = el.scrollLeft;
        sy = el.scrollTop;
        el.classList.add("grabbing");
    });
    el.addEventListener("pointermove", (e) => {
        if (!isDown) return;
        const dx = e.clientX - startX;
        const dy = e.clientY - startY;
        el.scrollLeft = sx - dx;
        el.scrollTop  = sy - dy;
    });
    const stop = () => { isDown = false; el.classList.remove("grabbing"); if (pid!=null) { try { el.releasePointerCapture(pid); } catch(_){} pid=null; } };
    el.addEventListener("pointerup", stop);
    el.addEventListener("pointerleave", stop);
    // Prevent accidental text/image dragging
    el.addEventListener("dragstart", (e) => e.preventDefault());
}