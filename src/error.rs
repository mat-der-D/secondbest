//! Error types for the game.
//!
//! This module defines various error types that can occur during game operations,
//! organized in a hierarchy from low-level bit operations to high-level game logic.

use crate::board::{Action, Position};
use thiserror::Error;

/// Errors related to low-level bit board operations.
#[derive(Debug, Clone, Error)]
pub enum BitBoardError {
    /// Indicates that a position is already occupied when trying to place a piece.
    #[error("Position is not available for placing pieces: {0:#x}")]
    PositionOccupied(u32),

    /// Indicates that a position is empty when a piece is expected.
    #[error("Empty position at bit position: {0:#x}")]
    EmptyPosition(u32),

    /// Indicates an invalid move between two positions.
    #[error("Invalid move from {from:#x} to {to:#x}")]
    InvalidMove { from: u32, to: u32 },
}

/// Errors related to board operations using logical positions.
#[derive(Debug, Clone, Error)]
pub enum BoardError {
    /// Indicates that a position is already occupied when trying to place a piece.
    #[error("Position already occupied: {0:?}")]
    PositionOccupied(Position),

    /// Indicates that a position is empty when a piece is expected.
    #[error("Empty position: {0:?}")]
    EmptyPosition(Position),

    /// Indicates an invalid move between two positions.
    #[error("Invalid move from {from:?} to {to:?}")]
    InvalidMove { from: Position, to: Position },

    /// Wraps a BitBoardError for propagation to higher levels.
    #[error(transparent)]
    BitBoardError(#[from] BitBoardError),
}

/// Errors related to game rules and state.
#[derive(Debug, Clone, Error)]
pub enum GameError {
    /// Indicates that an action violates the game rules.
    #[error("Illegal action: {0:?}")]
    IllegalAction(Action),

    /// Indicates that a second best declaration is not valid in the current state.
    #[error("Cannot declare second best")]
    CannotDeclareSecondBest,

    /// Indicates that an operation cannot be performed because the game has ended.
    #[error("Game is already over")]
    GameAlreadyOver,

    /// Wraps a BoardError for propagation to higher levels.
    #[error(transparent)]
    BoardError(#[from] BoardError),
}

/// Top-level error type that encompasses all possible errors in the game.
#[derive(Debug, Clone, Error)]
pub enum Error {
    /// Wraps a GameError.
    #[error(transparent)]
    Game(#[from] GameError),

    /// Wraps a BoardError.
    #[error(transparent)]
    Board(#[from] BoardError),

    /// Wraps a BitBoardError.
    #[error(transparent)]
    BitBoard(#[from] BitBoardError),

    /// Indicates an invalid position value.
    #[error("Position error: {0}")]
    Position(u32),

    /// Catch-all for other errors.
    #[error("Other error: {0}")]
    Other(String),
}
