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

// NOTE: Consider using a different diagonal calculation approach
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


// pred [p: Player, s: GameState, startRow: Int, startCol: Int, endRow: Int, endCol: Int] {
//     // The below checks that this move will flip some of the opponent's pieces.
//     // Given startRow, startCol, is there a continuous string of the other player's pieces
//     // "between" one of p's pieces and (row, col)

//         // The player p already has a piece at this position
//         s.board.contents[endRow][endCol] = playerToPiece[p]

//         // For everything between (startRow, startCol) and (endRow, endCol)
//         all betweenRow, betweenCol: Int | isBetween[startRow, startCol, endRow, endCol, betweenRow, betweenCol] implies {
//             // The opponent has a piece there
//             s.board.contents[betweenRow][betweenCol] = playerToPiece[oppositePlayer[p]]
//         }
// }

pred isValidMove[p: Player, s: GameState, startRow: Int, startCol: Int] {
    // Moving onto an empty tile
    s.board.contents[startRow][startCol] = Empty

    // Both row and column are valid indices
    validIndex[startRow] and validIndex[startCol]

    // The below checks that this move will flip some of the opponent's pieces.
    // Given startRow, startCol, is there a continuous string of the other player's pieces
    // "between" one of p's pieces and (row, col)
    some endRow, endCol: Int | {
        // The player p already has a piece at this position
        s.board.contents[endRow][endCol] = playerToPiece[p]

        // TODO: This is an efficiency bottleneck
        // For everything between (startRow, startCol) and (endRow, endCol)
        all betweenRow, betweenCol: Int | isBetween[startRow, startCol, endRow, endCol, betweenRow, betweenCol] implies {
            // The opponent has a piece there
            s.board.contents[betweenRow][betweenCol] = playerToPiece[oppositePlayer[p]]
        }
    }
}

pred canMove[p: Player, s: GameState] {
    some row, col: Int | isValidMove[p, s, row, col]
}

pred validFinal[s: GameState] {
    no p: Player | canMove[p, s]
}

pred validTransition[pre: GameState, post: GameState] {
    canMove[pre.turn, pre] implies {
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

pred correctFlipping[pre: GameState, post: GameState, moveRow: Int, moveCol: Int] {

    // TODO: This will have to check that flipping of pieces happens in ALL
    // the places where it should
    // All the other tiles remain the same
    // all endRow, endCol: Int | {
    //         (endRow != moveRow) or (endCol != moveCol)
    //         validIndex[endRow] 
    //         validIndex[endCol] 
    //         pre.board.contents[endRow][endCol] = playerToPiece[p]
    //     } implies {

    //         (all betweenRow, betweenCol: Int | {
    //             isBetween[moveRow, moveCol, endRow, endCol, betweenRow, betweenCol] implies
    //             pre.board.contents[betweenRow][betweenCol] = playerToPiece[oppositePlayer[p]]
    //         })
    //         implies {
    //             // The piece between these two bounds has flipped
    //             post.board.contents[betweenRow][betweenCol] = playerToPiece[p]
    //         } 
            
    
    //     }
    // }   

    all row, col: Int | (validIndex[row] and validIndex[col]) implies {

        // There is some other position where the player whose turn it is moved
        some endRow, endCol: Int | {
            (endRow != moveRow) or (endCol != moveCol)
            validIndex[endRow] 
            validIndex[endCol] 
            pre.board.contents[endRow][endCol] = playerToPiece[pre.turn] 

            // Everything between the move position and this position is the oppoent's pieces
            all betweenRow, betweenCol: Int | {
                isBetween[moveRow, moveCol, endRow, endCol, betweenRow, betweenCol] implies
                pre.board.contents[betweenRow][betweenCol] = playerToPiece[oppositePlayer[pre.turn]]
            }

            // (row, col) is contained within the outflanked section
            isBetween[moveRow, moveCol, endRow, endCol, row, col]
        }
        implies {
            // The piece has flipped
            post.board.contents[row][col] = playerToPiece[pre.turn]
        } else {
            // The piece has stayed the same
            post.board.contents[row][col] = pre.board.contents[row][col]
        }
    }
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

    // Flipping of opponent's pieces has occurred where appropriate
    correctFlipping[pre, post, row, col]
}

pred traces {
    validInit[Game.initialState]

    all s: GameState | some Game.next[s] implies {
        validTransition[s, Game.next[s]]
    }
}

run {
    Game.boardSize = 4
    all b: Board | validBoard[b]
    traces
}   for exactly 2 Player, exactly 3 Tile, exactly 1 Board, exactly 1 GameState, exactly 1 Game, exactly 4 Int
    for {next is linear}