#lang forge/bsl

// Two players: Black and White
abstract sig Player {}
one sig Black, White extends Player {}

// Tiles on the board can be:
//   1) Occupied by a black piece
//   2) Occupied by a white piece
//   3) Empty
abstract sig Tile {}
one sig BlackPiece, WhitePiece, Empty extends Tile {}

sig Board {
    contents: pfunc Int -> Int -> Tile 
}

sig GameState {
    turn: one Player,
    board: one Board
}

one sig Game {
    initialState: one GameState,
    boardSize: one Int,
    next: pfunc GameState -> GameState
}

// Determines if an index is within the bounds of the board (not negative
// and not above the size of the board minus one).
pred validIndex[index: Int] {
    0 <= index and index < Game.boardSize
}

// Determines if a board is valid based on the pieces that are in its contents.
pred validBoard[b: Board] {
    all row, col: Int | {
        (validIndex[row] and validIndex[col]) implies {
            // Within the valid range of the board, there must be a Tile
            some b.contents[row][col]
        } else {
            // Outside the board (negative indices or out of bounds), no Tiles
            no b.contents[row][col]
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
            init.board.contents[halfBoardMinusOne][halfBoardMinusOne] = WhitePiece
            init.board.contents[halfBoardMinusOne][halfBoard] = BlackPiece
            init.board.contents[halfBoard][halfBoardMinusOne] = BlackPiece
            init.board.contents[halfBoard][halfBoard] = WhitePiece

            // Every other cell on the board is empty
            all row, col: Int | {
                (validIndex[row] and validIndex[col]) implies {
                    not (
                        (row = halfBoard && col = halfBoard) or
                        (row = halfBoardMinusOne && col = halfBoard) or 
                        (row = halfBoardMinusOne && col = halfBoardMinusOne) or
                        (row = halfBoard && col = halfBoardMinusOne)
                    ) implies {
                        init.board.contents[row][col] = Empty
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
    #{row, col: Int | s.board.contents[row][col] = playerPiece} 
    > 
    #{row, col: Int | s.board.contents[row][col] = opponentPiece}
}

pred tie[s: GameState] {
    #{row, col: Int | s.board.contents[row][col] = BlackPiece}
    =
    #{row, col: Int | s.board.contents[row][col] = WhitePiece}
}

pred isBetweenBoundaries[bound1: Int, bound2: Int, position: Int] {
    (bound1 <= position and position <= bound2) or 
    (bound2 <= position and position <= bound1)
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

pred onDiagonal[row1: Int, col1: Int, row2: Int, col2: Int] {
    some offset: Int | {
        (add[row1, offset] = row2 and add[col1, offset] = col2) or
        (add[row1, offset] = row2 and subtract[col1, offset] = col2) or
        (subtract[row1, offset] = row2 and add[col1, offset] = col2) or
        (subtract[row1, offset] = row2 and subtract[col1, offset] = col2)
    }
}

pred isBetweenDiagonal[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    isBetweenBoundaries[startRow, endRow, row] and isBetweenBoundaries[startCol, endCol, col]

    // slope between start and end and also start and the position has to be 1 or -1
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

pred isValidMove[p: Player, s: GameState, row: Int, col: Int] {
    // TODO: Given row, col, is there a continuous string of the other player's pieces
    // "between" one of p's pieces and (row, col)
    // Note: Between needs to take into account horizontal, vertical, and diagonal


    // Something like this:
    // all row, col: Int | isBetween[...] implies other playre's pieces 

    // Moving onto an empty tile
    s.board.contents[row][col] = Empty

    // Both row and column are valid indices
    validIndex[row] and validIndex[col]
}

pred canMove[p: Player, s: GameState] {
    some row, col: Int | isValidMove[p, s, row, col]
}

pred validFinal[s: GameState] {
    no p: Player | canMove[p, s]
}

pred validTransition[pre: GameState, post: GameState] {
    canMove[pre.turn] implies {
        some row, col: Int | {
            move[pre, post, row, col]
        }
    } else {
        skip[pre, post]
    }
}

pred skip[pre: GameState, post: GameState] {
    // The player whose turn it is swaps
    post.turn != pre.turn

    // Everything else about the board stays the same
    all row, col: Int | pre.board.contents[row][col] = post.board.contents[row][col]
}

pred move[pre: GameState, post: GameState, row: Int, col: Int] {
    // == Guard - stuff true about pre == 

    // The game is not already over in the pre state
    not validFinal[pre]

    // Moving at (row, col) will capture some of the opponent's pieces and be valid
    isValidMove[pre.turn, pre, row, col]
    
    // == Action - what does the post-state look like == 

    // The turns have swapped from pre to post
    post.turn = {pre.turn = Black => White else Black}

    // The player whose turn it was put down their piece at (row, col)
    post.board.contents[row][col] = {pre.turn = Black => BlackPiece else WhitePiece}

    // All the other tiles remain the same
    all row2, col2: Int | (validIndex[row2] and validIndex[col2]) implies {
        ((row2 != row) or (col2 != col)) implies {
            // TODO: This is wrong - some of the pieces may flip, in which case they are not the same
            pre.board.contents[row2][col2] = post.board.contents[row2][col2]
        }
    }

    // TODO: This will have to check that flipping of pieces happens in ALL
    // the places where it should
}

run {
    Game.boardSize = 8
    validInit[Game.initialState]
    all b: Board | validBoard[b]
} for exactly 2 Player, 3 Tile, 1 Board, 1 GameState, 1 Game, 5 Int