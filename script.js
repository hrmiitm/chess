// script.js - two-player chess with a robust UI and interaction
(() => {
  // Unicode symbols for pieces
  const WHITE = 'w', BLACK = 'b';
  const SYMBOLS = {
    P: '♙', N: '♘', B: '♗', R: '♖', Q: '♕', K: '♔',
    p: '♟', n: '♞', b: '♝', r: '♜', q: '♛', k: '♚'
  };

  // Game state
  let board = [];
  let turn = WHITE; // White to move first
  let enPassant = null; // square {r,c} eligible for en passant capture
  let castling = { wK: true, wQ: true, bK: true, bQ: true };
  let selected = null; // {r,c}
  let legalMoves = []; // list of moves from selected piece
  let rotation = false; // board orientation
  let movesHistory = []; // simple stack of previous states for undo
  let lastMove = null; // {from,to,promo}
  let promotionPending = null; // {color, from, to}

  const boardEl = document.getElementById('board');
  const statusEl = document.getElementById('status');
  const movesEl = document.getElementById('moves');
  const capturedWhiteEl = document.getElementById('capturedWhite');
  const capturedBlackEl = document.getElementById('capturedBlack');
  const newGameBtn = document.getElementById('newGame');
  const undoBtn = document.getElementById('undo');
  const flipBtn = document.getElementById('flip');
  const promoModal = document.getElementById('promoModal');
  const promoOptions = document.getElementById('promoOptions');

  function initBoard() {
    // Standard initial position: white at bottom (rows 6-7)
    const whiteBack = ['R','N','B','Q','K','B','N','R'];
    const blackBack = ['r','n','b','q','k','b','n','r'];
    board = Array.from({ length: 8 }, () => Array(8).fill(null));
    // Black pieces on top
    for (let c = 0; c < 8; c++) board[0][c] = blackBack[c];
    for (let c = 0; c < 8; c++) board[1][c] = 'p';
    // Empty spaces
    for (let r = 2; r <= 5; r++) for (let c = 0; c < 8; c++) board[r][c] = null;
    // White pieces at bottom
    for (let c = 0; c < 8; c++) board[6][c] = 'P';
    for (let c = 0; c < 8; c++) board[7][c] = whiteBack[c];
  }

  function cloneBoard(b) {
    return b.map(row => row.slice());
  }

  function inBounds(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }

  function pieceAt(r, c) { return inBounds(r,c) ? board[r][c] : null; }
  function isWhite(p) { return p && p === p.toUpperCase(); }
  function pieceColor(p) { if (!p) return null; return isWhite(p) ? WHITE : BLACK; }
  function algebraic(r, c) {
    const file = String.fromCharCode('a'.charCodeAt(0) + c);
    const rank = 8 - r;
    return file + rank;
  }

  function isSquareAttackedBy(boardState, r, c, byColor) {
    // Check if square (r,c) is attacked by color byColor ('w' or 'b')
    // scan all pieces of that color and see if they attack (r,c)
    for (let rr = 0; rr < 8; rr++) {
      for (let cc = 0; cc < 8; cc++) {
        const p = boardState[rr][cc];
        if (!p) continue;
        if (pieceColor(p) !== byColor) continue;
        if (attacksSquare(boardState, rr, cc, r, c, p)) return true;
      }
    }
    return false;
  }

  function attacksSquare(boardState, fr, fc, tr, tc, p) {
    const color = pieceColor(p);
    const isWhiteP = color === WHITE;
    const dr = tr - fr;
    const dc = tc - fc;
    const absR = Math.abs(dr), absC = Math.abs(dc);

    const forward = isWhiteP ? -1 : 1; // direction of forward for pawns

    switch (p.toLowerCase()) {
      case 'p': {
        // Pawn attacks diagonally forward by one
        if (dr === forward && absC === 1) return true;
        return false;
      }
      case 'n': {
        const moves = [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];
        return moves.some(([r, c]) => fr + r === tr && fc + c === tc);
      }
      case 'b': {
        if (absR === absC && pathClear(boardState, fr, fc, tr, tc)) return true; else return false;
      }
      case 'r': {
        if ((dr === 0 || dc === 0) && pathClear(boardState, fr, fc, tr, tc)) return true; else return false;
      }
      case 'q': {
        if ((absR === absC || dr === 0 || dc === 0) && pathClear(boardState, fr, fc, tr, tc)) return true; else return false;
      }
      case 'k': {
        if (Math.max(absR, absC) === 1) return true; else return false;
      }
      default:
        return false;
    }
  }

  function pathClear(boardState, fr, fc, tr, tc) {
    const dr = Math.sign(tr - fr);
    const dc = Math.sign(tc - fc);
    let r = fr + dr, c = fc + dc;
    while (r !== tr || c !== tc) {
      if (boardState[r][c] !== null) return false;
      r += dr; c += dc;
    }
    return true;
  }

  function computeAllLegalMoves(color, b = board, enP = enPassant, cast = castling) {
    const moves = [];
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const p = b[r][c];
        if (!p) continue;
        if (pieceColor(p) !== color) continue;
        const pieceMoves = pseudoMovesForPiece(b, r, c, p, enP, cast);
        for (const mv of pieceMoves) {
          // simulate and ensure own king not in check
          const nb = cloneBoard(b);
          const captured = nb[mv.to.r][mv.to.c];
          applyMoveToBoard(nb, { from: { r, c }, to: mv.to, piece: p, promo: mv.promo }, null, null, false);
          const kingPos = findKing(nb, color);
          if (!kingPos) {
            // should not happen
            moves.push({ from: { r, c }, to: mv.to, piece: p, promo: mv.promo, captured });
            continue;
          }
          const inCheck = isSquareAttackedBy(nb, kingPos.r, kingPos.c, color === WHITE ? BLACK : WHITE);
          if (!inCheck) {
            moves.push({ from: { r, c }, to: mv.to, piece: p, promo: mv.promo, captured });
          }
        }
      }
    }
    // Castling moves are included in pseudo moves; we'll include as moves with to at (r,6) or (r,2)
    return moves;
  }

  function findKing(b, color) {
    const target = color === WHITE ? 'K' : 'k';
    for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++) if (b[r][c] === target) return { r, c };
    return null;
  }

  function pseudoMovesForPiece(b, r, c, p, enP, cast) {
    const moves = [];
    const color = pieceColor(p);
    const isWhiteP = color === WHITE;
    const dir = isWhiteP ? -1 : 1;
    const opp = isWhiteP ? BLACK : WHITE;
    switch (p.toLowerCase()) {
      case 'p': {
        // forward move
        const one = r + dir;
        if (inBounds(one, c) && b[one][c] === null) {
          // promotion handling not here; promote later
          if (one === 0 || one === 7) {
            moves.push({ to: { r: one, c }, promo: 'Q' });
          } else {
            moves.push({ to: { r: one, c } });
          }
          if ((r === 6 && isWhiteP) || (r === 1 && !isWhiteP)) {
            const two = r + 2*dir;
            if (inBounds(two, c) && b[two][c] === null) {
              moves.push({ to: { r: two, c } });
            }
          }
        }
        // captures
        for (const dc of [-1, 1]) {
          const tc = c + dc;
          const tr = r + dir;
          if (!inBounds(tr, tc)) continue;
          const target = b[tr][tc];
          if (target && pieceColor(target) === opp) {
            if (tr === 0 || tr === 7) {
              moves.push({ to: { r: tr, c: tc }, promo: 'Q' });
            } else {
              moves.push({ to: { r: tr, c: tc } });
            }
          }
        }
        // en passant
        if (enP) {
          if (r + dir === enP.r && Math.abs(c - enP.c) === 1) {
            moves.push({ to: { r: enP.r, c: enP.c }, enPassantCapture: true });
          }
        }
        break;
      }
      case 'n': {
        const deltas = [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];
        for (const [dr, dc] of deltas) {
          const nr = r+dr, nc = c+dc;
          if (!inBounds(nr,nc)) continue;
          const t = b[nr][nc];
          if (!t || pieceColor(t) !== color) {
            moves.push({ to: { r:nr, c:nc } });
          }
        }
        break;
      }
      case 'b': {
        const dirs = [[-1,-1],[-1,1],[1,-1],[1,1]];
        for (const [dr, dc] of dirs) {
          let nr = r+dr, nc = c+dc;
          while (inBounds(nr,nc)) {
            const t = b[nr][nc];
            if (!t) moves.push({ to: { r:nr, c:nc } });
            else {
              if (pieceColor(t) !== color) moves.push({ to: { r:nr, c:nc } });
              break;
            }
            nr += dr; nc += dc;
          }
        }
        break;
      }
      case 'r': {
        const dirs = [[-1,0],[1,0],[0,-1],[0,1]];
        for (const [dr, dc] of dirs) {
          let nr = r+dr, nc = c+dc;
          while (inBounds(nr,nc)) {
            const t = b[nr][nc];
            if (!t) moves.push({ to: { r:nr, c:nc } });
            else {
              if (pieceColor(t) !== color) moves.push({ to: { r:nr, c:nc } });
              break;
            }
            nr += dr; nc += dc;
          }
        }
        break;
      }
      case 'q': {
        const dirs = [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];
        for (const [dr, dc] of dirs) {
          let nr = r+dr, nc = c+dc;
          while (inBounds(nr,nc)) {
            const t = b[nr][nc];
            if (!t) moves.push({ to: { r:nr, c:nc } });
            else {
              if (pieceColor(t) !== color) moves.push({ to: { r:nr, c:nc } });
              break;
            }
            nr += dr; nc += dc;
          }
        }
        break;
      }
      case 'k': {
        for (let dr=-1; dr<=1; dr++) for (let dc=-1; dc<=1; dc++) {
          if (dr===0 && dc===0) continue;
          const nr = r+dr, nc = c+dc;
          if (!inBounds(nr,nc)) continue;
          const t = b[nr][nc];
          if (!t || pieceColor(t) !== color) moves.push({ to: { r:nr, c:nc } });
        }
        // castling availability
        if (color === WHITE && r === 7 && c === 4) {
          // white king side
          if (cast.wK && !b[7][5] && !b[7][6]) {
            // ensure squares not attacked
            if (!isSquareAttackedBy(b, 7, 4, BLACK) && !isSquareAttackedBy(b, 7, 5, BLACK) && !isSquareAttackedBy(b, 7, 6, BLACK)) {
              moves.push({ to: { r: 7, c: 6 }, isCastle: true, castle: 'K' });
            }
          }
          // white queen side
          if (cast.wQ && !b[7][3] && !b[7][2] && !b[7][1]) {
            if (!isSquareAttackedBy(b, 7, 4, BLACK) && !isSquareAttackedBy(b, 7, 3, BLACK) && !isSquareAttackedBy(b, 7, 2, BLACK)) {
              moves.push({ to: { r: 7, c: 2 }, isCastle: true, castle: 'Q' });
            }
          }
        } else if (color === BLACK && r === 0 && c === 4) {
          // black castling
          if (cast.bK && !b[0][5] && !b[0][6]) {
            if (!isSquareAttackedBy(b, 0, 4, WHITE) && !isSquareAttackedBy(b, 0, 5, WHITE) && !isSquareAttackedBy(b, 0, 6, WHITE)) {
              moves.push({ to: { r: 0, c: 6 }, isCastle: true, castle: 'K' });
            }
          }
          if (cast.bQ && !b[0][3] && !b[0][2] && !b[0][1]) {
            if (!isSquareAttackedBy(b, 0, 4, WHITE) && !isSquareAttackedBy(b, 0, 3, WHITE) && !isSquareAttackedBy(b, 0, 2, WHITE)) {
              moves.push({ to: { r: 0, c: 2 }, isCastle: true, castle: 'Q' });
            }
          }
        }
        break;
      }
    }
    // filter moves that land out of bounds etc already
    return moves;
  }

  function applyMoveToBoard(b, mv, origFrom=null, origTo=null, applyPromotion=true) {
    const from = mv.from ? mv.from : origFrom;
    const to = mv.to;
    const piece = mv.piece;
    if (!from) return;
    // handle en passant captures during manual use
    const capture = b[to.r][to.c];
  }

  function makeMove(moveObj) {
    // moveObj: {from:{r,c}, to:{r,c}, piece, promo?, isCastle?, castle?}
    const { from, to, piece, promo, isCastle } = moveObj;
    const color = pieceColor(piece);
    // handle en passant
    let captured = null;
    // if en passant capture
    if (moveObj.enPassantCapture) {
      const dir = color === WHITE ? 1 : -1;
      const capR = to.r + dir; // the captured pawn is directly behind destination
      captured = board[capR][to.c];
      board[to.r + 0][to.c] = null; // remove captured pawn? we'll adjust with actual coordinates below
    }

    // move piece
    board[to.r][to.c] = piece;
    board[from.r][from.c] = null;

    // promotion
    if (promo) {
      board[to.r][to.c] = color === WHITE ? promo : promo.toLowerCase();
    }

    // en passant capture fix (properly remove captured pawn when captured via en passant)
    if (moveObj.enPassantCapture) {
      const dir = color === WHITE ? 1 : -1;
      const capR = to.r + dir;
      board[capR][to.c] = null;
    }

    // castling: move rook accordingly and update rights
    if (isCastle) {
      if (moveObj.castle === 'K') {
        // white: king from e1(7,4) to g1(7,6); rook h1(7,7) to f1(7,5)
        if (color === WHITE) {
          board[7][5] = 'R';
          board[7][7] = null;
        } else {
          board[0][5] = 'r';
          board[0][7] = null;
        }
      } else if (moveObj.castle === 'Q') {
        // queen side: white a1(7,0) rook to d1(7,3)
        if (color === WHITE) {
          board[7][3] = 'R';
          board[7][0] = null;
        } else {
          board[0][3] = 'r';
          board[0][0] = null;
        }
      }
    }

    // update castling rights if king or rooks moved
    if (piece === 'K') { castling.wK = false; castling.wQ = false; }
    if (piece === 'k') { castling.bK = false; castling.bQ = false; }
    // if rook moved from initial squares
    if (from.r === 7 && from.c === 7) castling.wK = false;
    if (from.r === 7 && from.c === 0) castling.wQ = false;
    if (from.r === 0 && from.c === 7) castling.bK = false;
    if (from.r === 0 && from.c === 0) castling.bQ = false;

    // if pawn moved two squares, set enPassant target
    const movedPiece = piece; // after potential promotions
    if (movedPiece === 'P' || movedPiece === 'p') {
      if (Math.abs(to.r - from.r) === 2) {
        enPassant = { r: (from.r + to.r) / 2, c: from.c };
      } else {
        enPassant = null;
      }
    } else {
      enPassant = null;
    }
  }

  function renderBoard() {
    // render 8x8 board, with optional rotation
    boardEl.innerHTML = '';
    const squares = [];
    const base = rotation ? 0 : 7; // not used directly
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const cell = document.createElement('div');
        const rr = rotation ? 7 - r : r;
        const cc = rotation ? 7 - c : c;
        const piece = board[rr][cc];
        // color of square
        const isLight = ((rr + cc) % 2 === 0);
        cell.className = 'cell' + (isLight ? ' light' : ' dark');
        cell.dataset.r = rr;
        cell.dataset.c = cc;
        if (selected && selected.r === rr && selected.c === cc) {
          cell.classList.add('selected');
        }
        if (lastMove && lastMove.from && lastMove.from.r === rr && lastMove.from.c === cc) {
          cell.classList.add('last-move');
        }
        if (piece) {
          const span = document.createElement('span');
          span.className = 'piece';
          span.textContent = SYMBOLS[piece] || piece;
          cell.appendChild(span);
        }
        // click handler
        cell.addEventListener('click', () => onCellClick(rr, cc));
        boardEl.appendChild(cell);
        squares.push(cell);
      }
    }
  }

  function deselect() {
    selected = null; legalMoves = []; renderBoard(); updateStatus();
  }

  function onCellClick(r, c) {
    const p = board[r][c];
    if (selected) {
      // if clicked on a destination in legal moves
      const mv = legalMoves.find(m => m.to.r === r && m.to.c === c);
      if (mv) {
        // finalize move
        const piece = board[selected.r][selected.c];
        const isPromo = mv.promo ? true : false;
        const moveInfo = { from: { r: selected.r, c: selected.c }, to: { r, c }, piece: piece, promo: mv.promo };
        if (mv.isCastle) {
          moveInfo.isCastle = true; moveInfo.castle = mv.castle;
        }
        if (mv.enPassantCapture) moveInfo.enPassantCapture = true;
        // push snapshot for undo
        pushSnapshot();
        // apply move
        doMove(moveInfo);
        deselect();
        renderBoard();
        computeGameState();
        return;
      } else {
        // select new piece if own color
        if (p && pieceColor(p) === turn) {
          selected = { r, c };
          legalMoves = computeAllLegalMoves(turn, board, enPassant, castling).filter(m => m.from ? (m.from.r===r && m.from.c===c) : false);
          renderBoard();
          // highlight moves by adding temporary marks? handled in render
        } else {
          deselect();
        }
      }
    } else {
      // no piece selected yet
      if (p && pieceColor(p) === turn) {
        selected = { r, c };
        legalMoves = computeAllLegalMoves(turn);
        renderBoard();
      }
    }
  }

  function pushSnapshot() {
    const snapshot = {
      board: cloneBoard(board),
      turn, enPassant: enPassant ? { ...enPassant } : null,
      castling: { ...castling },
      lastMove: lastMove
    };
    movesHistory.push(snapshot);
  }

  function undoMove() {
    if (movesHistory.length === 0) return;
    const snap = movesHistory.pop();
    board = cloneBoard(snap.board);
    turn = snap.turn;
    enPassant = snap.enPassant ? { ...snap.enPassant } : null;
    castling = { ...snap.castling };
    lastMove = snap.lastMove || null;
    promotionPending = null;
    selected = null; legalMoves = [];
    renderBoard();
    updateStatus();
  }

  function doMove(moveInfo) {
    const { from, to, piece } = moveInfo;
    // capture handling
    let captured = board[to.r][to.c];
    // en passant capture handling
    if (moveInfo.enPassantCapture) {
      const dir = pieceColor(piece) === WHITE ? -1 : 1; // wrong? we want captured pawn behind to remove
      // However, for white pawn capturing en passant, captured pawn is at to.r+1
      const capR = to.r + (pieceColor(piece) === WHITE ? 1 : -1);
      captured = board[capR][to.c];
      board[capR][to.c] = null;
    }
    // Move piece
    board[to.r][to.c] = piece;
    board[from.r][from.c] = null;
    // promotion
    if (moveInfo.promo) {
      board[to.r][to.c] = (pieceColor(piece) === WHITE) ? moveInfo.promo : moveInfo.promo.toLowerCase();
    }
    // castling: rook move
    if (moveInfo.isCastle) {
      if (moveInfo.castle === 'K') {
        if (turn === WHITE) {
          board[7][5] = 'R'; board[7][7] = null;
        } else {
          board[0][5] = 'r'; board[0][7] = null;
        }
      } else if (moveInfo.castle === 'Q') {
        if (turn === WHITE) {
          board[7][3] = 'R'; board[7][0] = null;
        } else {
          board[0][3] = 'r'; board[0][0] = null;
        }
      }
    }
    // update lastMove
    lastMove = { from: { r: from.r, c: from.c }, to: { r: to.r, c: to.c } };
    // update enPassant
    enPassant = null;
    if (piece.toLowerCase() === 'p' && Math.abs(to.r - from.r) === 2) {
      enPassant = { r: (from.r + to.r) / 2, c: from.c };
    }
    // update castling rights
    if (piece === 'K') { castling.wK = false; castling.wQ = false; }
    if (piece === 'k') { castling.bK = false; castling.bQ = false; }
    if (from.r === 7 && from.c === 7) castling.wK = false;
    if (from.r === 7 && from.c === 0) castling.wQ = false;
    if (from.r === 0 && from.c === 7) castling.bK = false;
    if (from.r === 0 && from.c === 0) castling.bQ = false;

    // turn switch
    turn = (turn === WHITE) ? BLACK : WHITE;
  }

  function computeGameState() {
    // After a move, update status and checks
    const opp = (turn === WHITE) ? BLACK : WHITE; // next to move is opp
    const legal = computeAllLegalMoves(opp);
    const inCheck = isInCheck(opp);
    updateStatus(inCheck, legal.length === 0);
    // if no legal moves and inCheck -> checkmate; if none and not inCheck -> stalemate
    if (legal.length === 0) {
      if (inCheck) {
        statusEl.innerText = `Checkmate. ${turn === WHITE ? 'White' : 'Black'} wins`;
      } else {
        statusEl.innerText = 'Stalemate. Draw';
      }
    }
    renderBoard();
  }

  function isInCheck(color) {
    // find king of color
    const king = findKing(board, color);
    if (!king) return false;
    const enemy = color === WHITE ? BLACK : WHITE;
    return isSquareAttackedBy(board, king.r, king.c, enemy);
  }

  function updateStatus(inCheck=false, isMateOrStale=false) {
    const toMove = turn === WHITE ? 'White' : 'Black';
    statusEl.innerText = isInCheck(turn) ? `${toMove} to move. Check!` : `${toMove} to move`;
    if (inCheck && !isMateOrStale) {
      statusEl.innerText += ' (in check)';
    }
  }

  function renderMoveList() {
    movesEl.innerHTML = '';
    for (let i = 0; i < movesHistory.length; i++) {
      const li = document.createElement('li');
      li.textContent = movesHistory[i].move || '';
      movesEl.appendChild(li);
    }
  }

  // Setup controls
  newGameBtn.addEventListener('click', () => {
    initGameState();
    renderBoard();
    updateStatus();
  });
  undoBtn.addEventListener('click', () => {
    undoMove();
  });
  flipBtn.addEventListener('click', () => {
    rotation = !rotation; renderBoard();
  });

  // Promotion handling
  promoOptions.addEventListener('click', (e) => {
    const target = e.target.closest('[data-piece]');
    if (!target || !promotionPending) return;
    const piece = target.getAttribute('data-piece');
    promotionPending.promo = piece;
    // finalize promotion by applying move once user picks
    // moveInfo is stored on promotionPending
    const mv = promotionPending.moveInfo;
    mv.promo = piece;
    doMove(mv);
    promotionPending = null;
    promoModal.setAttribute('aria-hidden','true');
    promoModal.style.display = 'none';
    renderBoard();
    computeGameState();
  });

  // Init game
  function initGameState() {
    initBoard();
    turn = WHITE;
    enPassant = null;
    castling = { wK: true, wQ: true, bK: true, bQ: true };
    selected = null; legalMoves = [];
    movesHistory = [];
    lastMove = null;
    rotation = false;
  }

  function resetUIAndState() {
    initGameState();
    renderBoard();
  }

  function start() {
    initGameState();
    renderBoard();
    updateStatus();
  }

  // Start game on load
  initGameState();
  start();
})();
