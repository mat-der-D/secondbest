//! Board representation and manipulation for the Second Best game.
//!
//! # Board Representation
//!
//! The board consists of 8 positions arranged in a circle, where players can place
//! and move pieces. Each position can hold up to 3 pieces stacked vertically.
//! The board uses an efficient bit-based representation internally through the `BitBoard` struct.
//!
//! # Key Components
//!
//! - [`Board`]: High-level API for board manipulation
//! - [`BitBoard`]: Low-level bit-based board representation
//! - [`Position`]: Enumeration of the 8 board positions (N, NE, E, SE, S, SW, W, NW)
//! - [`PositionIter`]: Iterator over all board positions, returned by `Position::iter()`
//! - [`Color`]: Player colors (B for Black, W for White)
//! - [`Action`]: Game actions (Put or Move)
//! - [`LegalActionIter`]: Iterator for legal actions, returned by `Board::legal_action_iter`
//! - [`BitLegalPutIter`]: Iterator for legal piece placements, returned by `BitBoard::legal_put_iter`
//! - [`BitLegalMoveIter`]: Iterator for legal piece movements, returned by `BitBoard::legal_move_iter`
//!
//! # Example Usage
//!
//! ```
//! use secondbest::board::{Board, Position, Color, Action};
//!
//! // Create a new board (default empty)
//! let mut board = Board::default();
//!
//! // Place a piece
//! board.put(Position::N, Color::B).unwrap();
//!
//! // Check if a player has lined up (won)
//! if board.lines_up(Color::B) {
//!     println!("Black has lined up!");
//! }
//!
//! // Get all pieces at a position
//! let pieces = board.get_pieces_at(Position::N);
//! assert_eq!(pieces, vec![Color::B]);
//! ```
//!
//! # Using Iterators
//!
//! The library provides iterators to help you navigate legal actions:
//!
//! ```
//! use secondbest::board::{Board, Color, Action};
//!
//! let board = Board::default();
//!
//! // Iterate through all legal actions for a player
//! for action in board.legal_action_iter(Color::B) {
//!     match action {
//!         Action::Put(pos, color) => {
//!             println!("Can place {:?} at {:?}", color, pos);
//!         },
//!         Action::Move(from, to) => {
//!             println!("Can move from {:?} to {:?}", from, to);
//!         }
//!     }
//! }
//! ```
//!
//! # Iterating Over Positions
//!
//! You can iterate over all board positions using the `PositionIter`:
//!
//! ```
//! use secondbest::board::Position;
//!
//! // Iterate through all positions on the board
//! for position in Position::iter() {
//!     println!("Position: {:?}", position);
//! }
//! ```
//!
//! # Iterator Types
//!
//! The library exports several iterator types that are returned by various methods:
//!
//! - `PositionIter`: Returned by `Position::iter()`, provides all positions on the board
//! - `LegalActionIter`: Returned by `Board::legal_action_iter`, provides all legal actions (both puts and moves)
//! - `BitLegalPutIter`: Returned by `BitBoard::legal_put_iter`, provides legal piece placements at the bit level
//! - `BitLegalMoveIter`: Returned by `BitBoard::legal_move_iter`, provides legal piece movements at the bit level
//!
//! These types are exported to make them available for type annotations when needed, rather than
//! for direct construction or manipulation. Typically, you'll use them through the methods
//! that return them.

// ボードモジュールの定義と再エクスポート

// サブモジュールの宣言
pub mod bitboard;
pub mod board;
pub mod legal_actions;
pub mod types;

// 公開APIを再エクスポート
pub use bitboard::BitBoard;
pub use board::Board;
pub use legal_actions::{BitLegalMoveIter, BitLegalPutIter, LegalActionIter};
pub use types::{Action, Color, Position, PositionIter};
