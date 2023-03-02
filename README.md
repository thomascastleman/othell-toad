# othell-toad

Forge model of the game Othello for CSCI 1710.

# What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

Our project was to model the game of Othello. Othello is a 2 player game where one player plays with white tiles and the other plays with black tiles. The object of the game is to have more tiles of your color on the board than your opponent by the end of the game. Each play consists of adding a new tile of your color such that you can flip at least one of your opponents tiles. You can flip an opponent tile if you have another piece of your color such that all the tiles between this piece and the piece you are trying to play belong to your opponent. By surrounding your opponents pieces in this way, you flip all of their pieces on your turn. The game ends if the board is full or if neither you nor your opponent have any valid moves.

The main properties of the game that we modeled were having a valid initial state, having a valid ending state, and ensuring that each player would make valid moves between states. We also explored different conditions that could cause one player to always win or lose. In order to ensure that players were making valid moves between states, we first had to check if they had a valid move. If they did not, then their turn would be skipped. If they did have a move, we checked that the move they made was valid, and that all the pieces that should have been flipped would get flipped.

# Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

One design choice was to stick with smaller board sizes (in particular, 4x4) instead of the traditional 8x8 board. The
aim of this was to reduce the search space of game traces, so that Forge could terminate in a reasonable amount
of time and verify interesting properties of the game.

Additionally, in terms of optimizations, we introduced a set of `Int` in the `Game` sig (`Game.indexes`) that contains only the `Int`s that are valid board indices (in the case of 4x4, `0` through `3`). By quantifying over `Game.indexes` instead of `Int` in certain cases, we were able to improve performance.

We wrote several checks for properties that we thought were interesting and wanted to be able to answer about the game (but weren't sure of, based
on our intuition alone). For instance:

- **Can White win on a 4x4 board?** (We weren't sure, as Black always moves first and 4x4 is a nonstandard board)
- **Can one player eliminate _all_ of the pieces of the other player?** No, this is unsat.
- **Is a tie possible on the 4x4 board?** Yes, our model produces several valid tie instances.
- **Is it possible to flip corner pieces?** No, finding an instance where a corner piece is moved on and later flipped is unsat.
- **Can you win without making the last move?** No, there are no instances where the winner did not make the last move.
- **Can you lose if you control all four corners?** No, there are no instances where a player has all four corners and loses.

For visualization, we created a custom visualization script based on the Tic Tac Toe visualizer from lecture. It displays gameplay traces,
indicating White's pieces in white, Black's pieces in black, and empty spots in green.

> Note: The visualization script assumes there are 13 `GameState`s in the trace, and that the board size is 4x4.

# At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

## Sigs

```
abstract sig Player {}
one sig Black, White extends Player {}
```

These sigs represent the 2 players for the game, which are black and white.

```
abstract sig Tile {}
one sig BlackPiece, WhitePiece, Empty extends Tile {}
```

These sigs represent the values for each tile on the board. A single tile on the board can either be black or white, which means it belongs to a player, or empty, meaning that neither player has moved there yet.

```
sig GameState {
    turn: one Player,
    board: pfunc Int -> Int -> Tile
}
```

This sig represents a state in gameplay. It indicates whose turn it is (this is not necessarily
something that can be calculated by just looking at the board) and the contents of the board.

```
one sig Game {
    initialState: one GameState,
    boardSize: one Int,
    next: pfunc GameState -> GameState,
    indexes: set Int
}
```

This sig represents global properties of the game (such as dimensions of the board), and also encodes the linear sequence of game states via the `next` field.

## Predicates

> Note: We give an overview of the most important predicates below, but not all predicates are included.

```
pred validInit[init: GameState]
```

This predicate ensures that our initial state is a valid initial state with respect to the rules of the game. The game starts with 4 pieces in the center of the board layed out in a square. The top left and bottom right pieces belong to white and the top right and bottom left pieces belong to black. We also ensure that every other piece on the board is empty.

```
pred validFinal[s: GameState]
```

This predicate ensures that the last state of the game is a valid final state, which means that neither player can make a move. This would be true if there are no more empty tiles on the board or if there are no valid moves for either player.

```
pred validTransition[pre: GameState, post: GameState]
```

This predicate compares a pre GameState and a post GameState and ensures that the transition between the 2 of them aligns with what we would expect from correct game play. This means that either a player makes a valid more or the player skips their turn and the board remains the same. If a player can move, then we check that the move they made wasy valid. We check this by ensuring that there exists another piece of the players color such that all the pieces in between that piece and the piece that was just played belong to the opponent. This means that the player is able to flip some pieces and that move is valid. We then check that all the pieces are flipped correctly using a helper predicate correctFlipping[pre: GameState, post: GameState, moveRow: Int, moveCol: Int], which checks that the correct pieces on the board have been flipped between the pre state and the post state.

```
pred winning[p: Player]
```

This checks if a player p has more pieces that belong to them on the board than their opponent, which would determine that they have won.
