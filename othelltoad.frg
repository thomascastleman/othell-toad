#lang forge

// Two players: Black and White
abstract sig Player {}
one sig Black, White extends Player {}

// Tiles on the board can be:
//   1) Occupied by a black piece
//   2) Occupied by a white piece
//   3) Empty
abstract sig Tile {}
one sig BlackPiece, WhitePiece, Empty extends Tile {}

// sig Board {
//     contents: pfunc Int -> Int -> Tile 
// }

sig GameState {
    turn: one Player,
    board: pfunc Int -> Int -> Tile
}

one sig Game {
    initialState: one GameState,
    boardSize: one Int,
    next: pfunc GameState -> GameState,
    indexes: set Int
}

// Determines if an index is within the bounds of the board (not negative
// and not above the size of the board minus one).
pred validIndex[index: Int] {
    0 <= index and index < Game.boardSize
}

// Determines if a board is valid based on the pieces that are in its contents.
pred validBoard[s: GameState] {
    all row, col: Int | {
        (validIndex[row] and validIndex[col]) implies {
            // Within the valid range of the board, there must be a Tile
            some s.board[row][col]
        } else {
            // Outside the board (negative indices or out of bounds), no Tiles
            no s.board[row][col]
        }
    }
}

// Determines if the given Game has a valid initial state.
pred validInit[init: GameState] {
    let halfBoard = divide[Game.boardSize, 2] | {
        let halfBoardMinusOne = subtract[halfBoard, 1] | {
            // Black always moves first
            init.turn = Black

            // The middle 2x2 of the board has the starting pattern
            init.board[halfBoardMinusOne][halfBoardMinusOne] = WhitePiece
            init.board[halfBoardMinusOne][halfBoard] = BlackPiece
            init.board[halfBoard][halfBoardMinusOne] = BlackPiece
            init.board[halfBoard][halfBoard] = WhitePiece

            // Every other cell on the board is empty
            all row, col: Game.indexes | {
                (validIndex[row] and validIndex[col]) implies {
                    not (
                        (row = halfBoard && col = halfBoard) or
                        (row = halfBoardMinusOne && col = halfBoard) or 
                        (row = halfBoardMinusOne && col = halfBoardMinusOne) or
                        (row = halfBoard && col = halfBoardMinusOne)
                    ) implies {
                        init.board[row][col] = Empty
                    }
                }
            }
        }
    }
}

// This determines if player p has more pieces than their opponent in the given state.
pred morePieces[s: GameState, p: Player] {
    let playerPiece = {p = Black => BlackPiece else WhitePiece} |
    let opponentPiece = {p = Black => WhitePiece else BlackPiece} | 

    // The player has more pieces on the board than their opponent
    #{row, col: Int | s.board[row][col] = playerPiece} 
    > 
    #{row, col: Int | s.board[row][col] = opponentPiece}
}

pred tie[s: GameState] {
    #{row, col: Int | s.board[row][col] = BlackPiece}
    =
    #{row, col: Int | s.board[row][col] = WhitePiece}
}

pred isBetweenBoundaries[bound1: Int, bound2: Int, position: Int] {
    (bound1 < position and position < bound2) or 
    (bound2 < position and position < bound1)
}

pred isBetweenHorizontal[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    // All the rows are the same
    startRow = endRow and row = startRow
    // The column appears between the boundaries
    isBetweenBoundaries[startCol, endCol, col]
}

pred isBetweenVertical[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    // All columns are the same 
    startCol = endCol and col = startCol 
    // The row appears between the boundaries 
    isBetweenBoundaries[startRow, endRow, row]
}

// This function calculates the absolute difference between two integers
// Credit to Lab for this function.
fun absDifference(m: Int, n: Int): Int {
  let difference = subtract[m, n] {
    difference > 0 => difference else subtract[0, difference]
  }
}

pred onDiagonal[row1: Int, col1: Int, row2: Int, col2: Int] {
    absDifference[row1, row2] = absDifference[col1, col2]
}

pred isBetweenDiagonal[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    isBetweenBoundaries[startRow, endRow, row] and isBetweenBoundaries[startCol, endCol, col]

    // Slope between start and end and also start and the position has to be 1 or -1
    onDiagonal[startRow, startCol, endRow, endCol]
    onDiagonal[startRow, startCol, row, col]
}

// Determines if the given (row, col) is "between" the two positions (startRow, startCol)
// and (endRow, endCol), where between could mean along a row, column, or diagonal.
pred isBetween[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    isBetweenHorizontal[startRow, startCol, endRow, endCol, row, col] or 
    isBetweenVertical[startRow, startCol, endRow, endCol, row, col] or 
    isBetweenDiagonal[startRow, startCol, endRow, endCol, row, col]
}

fun playerToPiece(p: Player): Tile {
    {p = Black => BlackPiece else WhitePiece}
}

fun oppositePlayer(p: Player): Player {
    {p = Black => White else Black}
}

pred isValidMove[p: Player, s: GameState, startRow: Int, startCol: Int] {
    // Moving onto an empty tile
    s.board[startRow][startCol] = Empty

    // Both row and column are valid indices
    validIndex[startRow] and validIndex[startCol]

    // The below checks that this move will flip some of the opponent's pieces.
    // Given startRow, startCol, is there a continuous string of the other player's pieces
    // "between" one of p's pieces and (row, col)
    some endRow, endCol: Game.indexes | {
        validIndex[endRow] and validIndex[endCol]

        // The player p already has a piece at this position
        s.board[endRow][endCol] = playerToPiece[p]

        // For everything between (startRow, startCol) and (endRow, endCol)
        all betweenRow, betweenCol: Game.indexes | {
            validIndex[betweenRow] and validIndex[betweenCol]
            isBetween[startRow, startCol, endRow, endCol, betweenRow, betweenCol]
            } implies {
            // The opponent has a piece there
            s.board[betweenRow][betweenCol] = playerToPiece[oppositePlayer[p]]
        }
    }
}

pred canMove[p: Player, s: GameState] {
    some row, col: Game.indexes | isValidMove[p, s, row, col]
}

pred validFinal[s: GameState] {
    no p: Player | canMove[p, s]
}

pred validTransition[pre: GameState, post: GameState] {
    // The turns have swapped from pre to post
    post.turn = oppositePlayer[pre.turn]

    canMove[pre.turn, pre] implies {
        some startRow, startCol: Game.indexes | {
            // Moving onto an empty tile
            pre.board[startRow][startCol] = Empty

            // Both row and column are valid indices
            validIndex[startRow] and validIndex[startCol]

            // The below checks that this move will flip some of the opponent's pieces.
            // Given startRow, startCol, is there a continuous string of the other player's pieces
            // "between" one of p's pieces and (row, col)
            some endRow, endCol: Game.indexes | {
                (endRow != startRow or endCol != startCol)
                validIndex[endRow] and validIndex[endCol]

                // The player p already has a piece at this position
                pre.board[endRow][endCol] = playerToPiece[pre.turn]

                // There is at least ONE tile that will be flipped by this move
                some betweenRow, betweenCol: Game.indexes | {
                    validIndex[betweenRow] and validIndex[betweenCol]
                    isBetween[startRow, startCol, endRow, endCol, betweenRow, betweenCol]
                    pre.board[betweenRow][betweenCol] = playerToPiece[oppositePlayer[pre.turn]]
                }

                // For everything between (startRow, startCol) and (endRow, endCol)
                all betweenRow, betweenCol: Game.indexes | {
                    {
                        validIndex[betweenRow] and validIndex[betweenCol]
                        isBetween[startRow, startCol, endRow, endCol, betweenRow, betweenCol]
                    } implies {
                        // The opponent has a piece there
                        pre.board[betweenRow][betweenCol] = playerToPiece[oppositePlayer[pre.turn]]
                    }
                }
            }

            // The player whose turn it was put down their piece at (row, col)
            post.board[startRow][startCol] = playerToPiece[pre.turn]

            // Flipping of opponent's pieces has occurred where appropriate
            correctFlipping[pre, post, startRow, startCol]
        }
    } else {
        skip[pre, post]
    }
}

pred skip[pre: GameState, post: GameState] {
    // Everything else about the board stays the same
    all row, col: Game.indexes | {
        (validIndex[row] and validIndex[col]) implies {
            pre.board[row][col] = post.board[row][col]
        }
    }

    // After the skip, the opponent will be able to make a move (otherwise, the game is over)
    canMove[oppositePlayer[pre.turn], post]
}

pred correctFlipping[pre: GameState, post: GameState, moveRow: Int, moveCol: Int] {
    // All tiles either flip from one piece to the other, or stay the same - except for
    // the move position, which goes from empty to a tile.
    all row, col: Game.indexes | (validIndex[row] and validIndex[col] and (row != moveRow or col != moveCol)) implies {
        // There is some other position where the player whose turn it is moved
        (some endRow, endCol: Game.indexes | {
            (endRow != moveRow) or (endCol != moveCol)
            validIndex[endRow] 
            validIndex[endCol] 
            pre.board[endRow][endCol] = playerToPiece[pre.turn] 

            // Everything between the move position and this position is the opponent's pieces
            all betweenRow, betweenCol: Game.indexes | {
                {
                    validIndex[betweenRow] and validIndex[betweenCol]
                    isBetween[moveRow, moveCol, endRow, endCol, betweenRow, betweenCol]
                 } implies {
                    pre.board[betweenRow][betweenCol] = playerToPiece[oppositePlayer[pre.turn]]
                 }
            }

            // (row, col) is contained within the outflanked section
            isBetween[moveRow, moveCol, endRow, endCol, row, col]
        })
        implies {
            // The piece has flipped
            post.board[row][col] = playerToPiece[pre.turn]
        } else {
            // The piece has stayed the same
            post.board[row][col] = pre.board[row][col]
        }
    }
}

pred traces {
    validInit[Game.initialState]

    // No state comes before the initial state
    no pre: GameState | Game.next[pre] = Game.initialState

    all s: GameState | some Game.next[s] implies {
        validTransition[s, Game.next[s]]
    }
}


// This restricts the contents field to use only 0-3 Ints
inst optimizer_size4_1board {
    GameState = `GameState0
    BlackPiece = `BlackPiece
    WhitePiece = `WhitePiece
    Empty = `Empty
    Tile = BlackPiece + WhitePiece + Empty

    board in GameState -> (0 + 1 + 2 + 3) -> (0 + 1 + 2 + 3) -> Tile

    Game = `Game0
    boardSize = `Game0 -> 4

    indexes = `Game0 -> (0 + 1 + 2 + 3)
}

inst optimizer_size4_2board {
    GameState = `GameState0 + `GameState1
    BlackPiece = `BlackPiece
    WhitePiece = `WhitePiece
    Empty = `Empty
    Tile = BlackPiece + WhitePiece + Empty

    board in GameState -> (0 + 1 + 2 + 3) -> (0 + 1 + 2 + 3) -> Tile

    Game = `Game0
    boardSize = `Game0 -> 4

    indexes = `Game0 -> (0 + 1 + 2 + 3)
}

inst optimizer_size4_3board {
    // GameState = `GameState0 + `GameState1 + `GameState2
    BlackPiece = `BlackPiece
    WhitePiece = `WhitePiece
    Empty = `Empty
    Tile = BlackPiece + WhitePiece + Empty

    // board in GameState -> (0 + 1 + 2 + 3) -> (0 + 1 + 2 + 3) -> Tile

    Game = `Game0
    boardSize = `Game0 -> 4

    indexes = `Game0 -> (0 + 1 + 2 + 3)
}

// Can White win on a 4x4 board?
// Yes
run {
    Game.boardSize = 4
    all s: GameState | validBoard[s]
    traces
    
    some final: GameState | {
        // It is the last state
        no Game.next[final]

        // White has more pieces in the final state (they won)
        morePieces[final, White]
    }

} for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
for {
    optimizer_size4_3board
    next is linear
}

option skolem_depth 2
option sb 2000
option verbose 5

// For debugging info:
// option verbose 5

// The 4 billion figure shouldn't be a prob for Forge

// Guards for valid indices not present for endRow/endCol in isValidMove
// and also for betweenRow and betweenCol


// use inst with 
//      contents in Board -> (0 1 2 3 4) -> (0 1 2 3 4) -> Tile
// 

// Fixing the board size may allow some optimizations

// Because we are counting pieces, our Int size needs to be big enough to accommodate that

// Other options to try:
// option skolem_depth 2
// option sb 2000

// NOTE: We're not actually using morePieces or tie anywhere right now