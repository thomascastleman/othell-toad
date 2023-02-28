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
    // No state comes before this one
    no pre: GameState | Game.next[pre] = init
    
    // The board configuration is valid
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

// Counts how many pieces the given player has on the board of this state.
fun countPieces(s: GameState, p: Player): Int {
    #{row, col: Game.indexes | s.board[row][col] = playerToPiece[p]} 
}

// This determines if player p has more pieces than their opponent in the given state.
pred morePieces[s: GameState, p: Player] {
    countPieces[s, p] > countPieces[s, oppositePlayer[p]]
}

// Determines if the given game state represents a tie (same number of pieces for both players).
pred tie[s: GameState] {
    countPieces[s, White] = countPieces[s, Black]
}

// Checks if the given position is between (exclusive) the given bounds,
// regardless of the ordering of the bounds (bound1 < bound2 or bound2 < bound1).
pred isBetweenBoundaries[bound1: Int, bound2: Int, position: Int] {
    (bound1 < position and position < bound2) or 
    (bound2 < position and position < bound1)
}

// Checks if the given (row, col) is between (startRow, startCol) and (endRow, endCol)
// along a row (horizontally).
pred isBetweenHorizontal[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    // All the rows are the same
    startRow = endRow and row = startRow
    // The column appears between the boundaries
    isBetweenBoundaries[startCol, endCol, col]
}

// Checks if the given (row, col) is between (startRow, startCol) and (endRow, endCol)
// along a column (vertically).
pred isBetweenVertical[startRow: Int, startCol: Int, endRow: Int, endCol: Int, row: Int, col: Int] {
    // All columns are the same 
    startCol = endCol and col = startCol 
    // The row appears between the boundaries 
    isBetweenBoundaries[startRow, endRow, row]
}

// This function calculates the absolute difference between two integers.
// Credit to N-Queens lab for this function.
fun absDifference(m: Int, n: Int): Int {
  let difference = subtract[m, n] {
    difference > 0 => difference else subtract[0, difference]
  }
}

// Checks if (row1, col1) and (row2, col2) are on the same diagonal.
pred onDiagonal[row1: Int, col1: Int, row2: Int, col2: Int] {
    absDifference[row1, row2] = absDifference[col1, col2]
}

// Checks if (row, col) is between (startRow, startCol) and (endRow, endCol) diagonally.
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

// Converts a player to their piece.
fun playerToPiece(p: Player): Tile {
    {p = Black => BlackPiece else WhitePiece}
}

// Converts a player to their opponent
fun oppositePlayer(p: Player): Player {
    {p = Black => White else Black}
}

// Checks if moving at (startRow, startCol) is valid for player p in this game state.
// A valid move must flip at least one of the opponent's pieces.
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
            {
                validIndex[betweenRow] and validIndex[betweenCol]
                isBetween[startRow, startCol, endRow, endCol, betweenRow, betweenCol]
            } implies {
                // The opponent has a piece there
                s.board[betweenRow][betweenCol] = playerToPiece[oppositePlayer[p]]
            }
        }
    }
}

// Determines if the given player can make any valid move from the given game state.
pred canMove[p: Player, s: GameState] {
    some row, col: Game.indexes | isValidMove[p, s, row, col]
}

// Determines if this game state is a final state.
pred validFinal[s: GameState] {
    // Neither player can move
    no p: Player | canMove[p, s]
    // This state has no successor in the trace
    no Game.next[s]
}

// Checks if a transition from the pre state to the post state abides by the rules of Othello.
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

// Determines if the transition from the pre state to the post state indicates
// a valid situation where a player's turn was skipped because they could not make a move.
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

// Checks that, in a transition from pre to post where the player whose turn it is
// moves at (moveRow, moveCol), all the pieces that need to flip do indeed flip,
// and all pieces that need to stay the same do so.
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

// Checks that this instance constitutes a valid trace of the game. That is,
// it represents a full playthrough from start to finish, and all transitions
// between states abide by the rules.
pred traces {
    // The initial state is a valid initial state
    validInit[Game.initialState]

    // There is a state which is a valid final state
    some final: GameState | {
        validFinal[final]
    }

    all s: GameState | {
        // State has a valid board (no crazy out of bounds indices)
        validBoard[s] 

        // All of the transitions as indicated by Game.next are valid
        some Game.next[s] implies {
            validTransition[s, Game.next[s]]
        }
    }
}

// Checks if the given player wins in this instance. Assumes traces.
pred winning[p: Player] {
    some final: GameState | {
        // It is the last state
        no Game.next[final]

        // Player p has more pieces in the final state (they won)
        morePieces[final, p]
    }
}

// Determines if the given position is one of the four corners of the board.
pred isCorner[row: Int, col: Int] {
    // Corners are (0, 0) (0, maxIndex) (maxIndex, 0) (maxIndex, maxIndex)
    let maxIndex = subtract[Game.boardSize, 1] | {
        row = 0 or row = maxIndex
        col = 0 or col = maxIndex
    }
}

// This optimizer restricts Game.indexes to only the Ints that are valid
// indices into the board. There are several places where we quantify over
// Game.indexes instead of Int in order to reduce the possibilities Forge has
// to quantify over.
inst optimizer_for_4x4_board {
    BlackPiece = `BlackPiece0
    WhitePiece = `WhitePiece0
    Empty = `Empty0
    Tile = BlackPiece + WhitePiece + Empty

    Game = `Game0
    boardSize = `Game0 -> 4
    indexes = `Game0 -> (0 + 1 + 2 + 3)
}

// ======================== Checking Properties ======================== 

// Can White win on a 4x4 board? Yes
// run {
//     Game.boardSize = 4
//     traces
//     winning[White]
// } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
// for {
//     optimizer_for_4x4_board
//     next is linear
// }

// Can Black win by eliminating all of the White pieces? No, this is unsat.
// Same for vice versa.
// run {
//     Game.boardSize = 4
//     traces

//     some s: GameState |  { 
//         // This state is final
//         no Game.next[s]

//         // All of the tiles are Black or empty
//         all row, col: Game.indexes | {
//             validIndex[row]
//             validIndex[col]
//             (s.board[row][col] = playerToPiece[Black]) or (s.board[row][col] = Empty)
//         }
//     }
// } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
// for {
//     optimizer_for_4x4_board
//     next is linear
// }

// Can there be a tie on a 4x4 board? Yes. There are several valid instances.
// run {
//     Game.boardSize = 4
//     traces

//     some final: GameState |  { 
//         no Game.next[final] // This is the final state
//         tie[final]          // It is a tie
//     }
// } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
// for {
//     optimizer_for_4x4_board
//     next is linear
// }

// Once you place a piece in a corner, it can never flip.
// This run attempts to find a trace where one player moves in a corner
// and then that corner is later flipped.
// This is unsat, so corner pieces can never be flipped.
// run {
//     Game.boardSize = 4
//     traces

//     // Find me a corner
//     some cornerRow, cornerCol: Int | {
//         isCorner[cornerRow, cornerCol]

//         some earlierState, laterState: GameState | {
//             // The later state occurs after the earlier state
//             reachable[laterState, earlierState, Game.next]

//             some player: Player | {
//                 // This player moves at this corner in the earlier state
//                 earlierState.board[cornerRow][cornerCol] = playerToPiece[player]

//                 // The opponent flips this corner in the later state
//                 laterState.board[cornerRow][cornerCol] = playerToPiece[oppositePlayer[player]]
//             }
//         }
//     }
// } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
// for {
//     optimizer_for_4x4_board
//     next is linear
// }

// This run checks if you can win the game without having the last move. 
// Tested where black wins and white had the last move, and where white wins and black has the last move
// This was unsat, meaning that there was no instance where a player did not have the last move and still won
// run {
//     Game.boardSize = 4
//     traces

//     some final: GameState |  { 
//         no Game.next[final] // This is the final state
//         final.turn = White      //Black had the last move
//         winning[White]          //White wins
//     }
// } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
// for {
//     optimizer_for_4x4_board
//     next is linear
// }

//This run checks if Black can win even if White controls all the corners, or vice-versa. 
//This is unsat. It is not possible for the a player to win if the other player controls all the corners. 

//Check if Black wins when White has the corners - unsat
// run {
//     Game.boardSize = 4
//     traces

//     some final: GameState |  { 
//         no Game.next[final] // This is the final state
//         winning[Black]          //Black wins

//         //White has all the corners
//         all row, col: Game.indexes | isCorner[row, col] implies {
//             final.board[row, col] = playerToPiece[White]
//         }
//     }
// } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
// for {
//     optimizer_for_4x4_board
//     next is linear
// }

//Check if White wins when Black has all the corners - unsat
run {
    Game.boardSize = 4
    traces

    some final: GameState |  { 
        no Game.next[final] // This is the final state
        winning[White]          //White wins

        //Black has all the corners
        all row, col: Game.indexes | isCorner[row, col] implies {
            final.board[row, col] = playerToPiece[Black]
        }
    }
} for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
for {
    optimizer_for_4x4_board
    next is linear
}
