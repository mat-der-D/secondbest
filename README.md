# secondbest

`secondbest` is a Rust library for implementing the "Second Best" strategy game. This library
provides a complete implementation of the game rules, board representation, and game state management.

## Game Overview

"Second Best" is a strategic board game played on 8 positions arranged in a circle. Players take turns
placing pieces of their color (Black or White) or moving pieces already on the board. The game features
a unique mechanic where a player can declare "second best" after their opponent's move, forcing the opponent
to choose a different action.

### Winning Conditions

A player wins when they achieve one of the following:
- Stack 3 of their pieces in a single position (vertical line-up)
- Have their pieces at the top of 4 consecutive positions (horizontal line-up)
- If both players achieve a winning condition simultaneously, the player who made the last move wins
- If a player has no legal moves available, they lose

Note: Winning conditions are only checked after all "second best" declarations have been used.

## Architecture

The library is organized into several modules:

- `board`: Core board representation and operations
  - `BitBoard`: Low-level bit manipulation for efficient board state representation
  - `Board`: High-level API for board manipulation
  - `Position`: Enumeration of the 8 board positions (N, NE, E, SE, S, SW, W, NW)
  - `Color`: Player colors (B for Black, W for White)
  - `Action`: Game actions (Put or Move)

- `game`: Game state management
  - `Game`: Main game state controller
  - `GameResult`: Game outcome representation

- `error`: Error handling
  - Various error types for different operations

## Basic Usage

```rust
use secondbest::prelude::*;

// Create a new game
let mut game = Game::new();

// Apply actions (place pieces and move them)
game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
game.apply_action(Action::Put(Position::S, Color::W)).unwrap();

// Check game state
if game.can_declare_second_best() {
    game.declare_second_best().unwrap();
}

// Check for a winner
match game.result() {
    GameResult::Finished { winner } => println!("Winner: {:?}", winner),
    GameResult::InProgress => println!("Game still in progress"),
}
```

## Advanced Usage

For lower-level control, you can work directly with the `Board` API:

```rust
use secondbest::prelude::*;

let mut board = Board::default();

// Place pieces
board.put(Position::N, Color::B).unwrap();

// Check board state
let pieces_at_north = board.get_pieces_at(Position::N);
let black_piece_count = board.count_pieces(Color::B);

// Check for winning conditions
if board.lines_up(Color::B) {
    println!("Black has won!");
}
```

## Error Handling

The library provides detailed error types for various operations:

```rust
use secondbest::prelude::*;
use secondbest::error::GameError;

let mut game = Game::new();
let result = game.apply_action(Action::Put(Position::N, Color::B));

match result {
    Ok(()) => println!("Action applied successfully"),
    Err(GameError::IllegalAction(_)) => println!("Illegal action"),
    Err(GameError::GameAlreadyOver) => println!("Game is already over"),
    Err(GameError::BoardError(_)) => println!("Board error occurred"),
    Err(_) => println!("Other error occurred"),
}
```

License: MIT OR Apache-2.0
