const d3 = require('d3')
d3.selectAll("svg > *").remove();

const BOARD_SIZE = 4;

function showPiece(color, row, col, xoffset, yoffset) {
    d3.select(svg)
        .append('rect')
        .attr("x", (row+1)*16 + xoffset)
        .attr("y", (col+1)*16 + yoffset)
        .attr('width', 16)
        .attr('height', 16)
        .attr('stroke-width', 1)
        .attr('stroke', 'black')
        .attr('fill', color);
}

function printValue(row, col, xoffset, yoffset, value) {
    console.log(value);
    if (value == "WhitePiece0") {
        showPiece("white", row, col, xoffset, yoffset);
    } else if (value == "BlackPiece0") {
        showPiece("black", row, col, xoffset, yoffset);
    } else if (value == "Empty0") {
        showPiece("#00b33c", row, col, xoffset, yoffset);
    }

}

function printState(stateAtom, xoffset, yoffset) {
  for (r = 0; r < BOARD_SIZE; r++) {
    for (c = 0; c < BOARD_SIZE; c++) {
      printValue(r, c, xoffset, yoffset,
                 stateAtom.board[r][c]
                 .toString())  
    }
  }
}

var yoffset = 0;
var xoffset = 0;

var STATES_PER_COLUMN = 4;

for(b = 0; b < 13; b++) {  
  if (b > 0 && b % STATES_PER_COLUMN == 0) {
      xoffset = xoffset + 80;
      yoffset = 0;
  }
  if(GameState.atom("GameState"+b) != null) {
    printState(GameState.atom("GameState"+b), xoffset, yoffset);
  }

  yoffset = yoffset + 80
}