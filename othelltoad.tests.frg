#lang forge

open "othelltoad.frg"

test expect {
    NegativeIndicesAreValid: {
        Game.boardSize = 4

        // Some valid state has something at a negative index on the board
        some s: GameState | {
            validBoard[s]
            some row, col: Int | {
                row < 0 or col < 0
                some s.board[row][col]
            }
        }
    } for exactly 2 Player, exactly 3 Tile, exactly 1 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear 
    } is unsat

    // Can White win on a 4x4 board? Yes
    WhiteWinsOn4x4: {
        Game.boardSize = 4
        traces
        winning[White]
    } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear
    } is sat

    // Can Black win by eliminating all of the White pieces? No, this is unsat.
    // Same for vice versa.
    // TODO: Make generic for both players
    BlackWipesOutWhite: {
        Game.boardSize = 4
        traces

        some s: GameState |  { 
            // This state is final
            no Game.next[s]

            // All of the tiles are Black or empty
            all row, col: Game.indexes | {
                validIndex[row]
                validIndex[col]
                (s.board[row][col] = playerToPiece[Black]) or (s.board[row][col] = Empty)
            }
        }
    } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear
    } is unsat

    // Can there be a tie on a 4x4 board? Yes. There are several valid instances.
    TieIsPossible: {
        Game.boardSize = 4
        traces

        some final: GameState |  { 
            no Game.next[final] // This is the final state
            tie[final]          // It is a tie
        }
    } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear
    } is sat

    // Once you place a piece in a corner, it can never flip.
    // This run attempts to find a trace where one player moves in a corner
    // and then that corner is later flipped.
    // This is unsat, so corner pieces can never be flipped.
    CornersCanFlip: {
        Game.boardSize = 4
        traces

        // Find me a corner
        some cornerRow, cornerCol: Int | {
            isCorner[cornerRow, cornerCol]

            some earlierState, laterState: GameState | {
                // The later state occurs after the earlier state
                reachable[laterState, earlierState, Game.next]

                some player: Player | {
                    // This player moves at this corner in the earlier state
                    earlierState.board[cornerRow][cornerCol] = playerToPiece[player]

                    // The opponent flips this corner in the later state
                    laterState.board[cornerRow][cornerCol] = playerToPiece[oppositePlayer[player]]
                }
            }
        }
    } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear
    } is unsat

    // This run checks if you can win the game without having the last move. 
    // Tested where black wins and white had the last move, and where white wins and black has the last move
    // This was unsat, meaning that there was no instance where a player did not have the last move and still won
    WhiteWinsWithoutLastMove: {
        Game.boardSize = 4
        traces

        some final: GameState |  { 
            no Game.next[final] // This is the final state
            final.turn = White      //Black had the last move
            winning[White]          //White wins
        }
    } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear
    } is unsat

    // This run checks if Black can win even if White controls all the corners, or vice-versa. 
    // This is unsat. It is not possible for the a player to win if the other player controls all the corners. 
    // Check if Black wins when White has the corners - unsat
    BlackWinsWhiteHasCorners: {
        Game.boardSize = 4
        traces

        some final: GameState |  { 
            no Game.next[final] // This is the final state
            winning[Black]          //Black wins

            //White has all the corners
            all row, col: Game.indexes | isCorner[row, col] implies {
                final.board[row, col] = playerToPiece[White]
            }
        }
    } for exactly 2 Player, exactly 3 Tile, 13 GameState, exactly 1 Game, exactly 5 Int
    for {
        optimizer_for_4x4_board
        next is linear
    } is unsat

    // Check if White wins when Black has all the corners - unsat
    WhiteWinsBlackHasCorners: {
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
    } is unsat

}