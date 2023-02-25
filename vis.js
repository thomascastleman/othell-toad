
const BOARD_SIZE = 4;

const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, yoffset, value) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .attr("x", (row+1)*10)
    .attr("y", (col+1)*14 + yoffset)
    .text(value);
}

function printState(stateAtom, yoffset) {
  for (r = 0; r < BOARD_SIZE; r++) {
    for (c = 0; c < BOARD_SIZE; c++) {
      printValue(r, c, yoffset,
                 stateAtom.board[r][c]
                 .toString());
    }
  }
  
  d3.select(svg)
    .append('rect')
    .attr('x', 5)
    .attr('y', yoffset+1)
    .attr('width', 40)
    .attr('height', 50)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
}


var offset = 0
for(b = 0; b <= 1; b++) {  
  if(GameState.atom("GameState"+b) != null)
    printState(GameState.atom("GameState"+b), offset)  
  offset = offset + 55
}