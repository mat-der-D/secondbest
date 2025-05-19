//! Types and enums for the game board.
//!
//! This module defines the core types used to represent the game board, including:
//! - `Position`: Represents positions on the circular board
//! - `Color`: Represents piece colors (Black and White)
//! - `Action`: Represents possible game actions (Put and Move)
//! - `PositionIter`: Iterator for board positions
//!
//! These types provide a high-level representation of the game elements, built on top
//! of the efficient bit-based implementation in the `bitboard` module.

/// Represents a position on the game board.
///
/// The board consists of 8 positions arranged in a circle, named after cardinal and intercardinal directions.
/// Each position is represented by a specific bit pattern for efficient bit-based operations.
///
/// # Examples
///
/// ```
/// use secondbest::board::Position;
///
/// // Using a specific position
/// let north_position = Position::N;
///
/// // Iterating through all positions
/// for position in Position::iter() {
///     println!("Position: {:?}", position);
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum Position {
    /// North position (bit pattern: 0x0000_0008)
    N = 0x0000_0008,
    /// Northeast position (bit pattern: 0x0000_0080)
    NE = 0x0000_0080,
    /// East position (bit pattern: 0x0000_0800)
    E = 0x0000_0800,
    /// Southeast position (bit pattern: 0x0000_8000)
    SE = 0x0000_8000,
    /// South position (bit pattern: 0x0008_0000)
    S = 0x0008_0000,
    /// Southwest position (bit pattern: 0x0080_0000)
    SW = 0x0080_0000,
    /// West position (bit pattern: 0x0800_0000)
    W = 0x0800_0000,
    /// Northwest position (bit pattern: 0x8000_0000)
    NW = 0x8000_0000,
}

impl Position {
    /// Creates a Position from a u32 value without checking if it's valid.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not verify that the input value
    /// represents a valid Position. The caller must ensure that the value is one
    /// of the valid bit patterns defined in the Position enum.
    pub(crate) unsafe fn from_u32_unchecked(value: u32) -> Self {
        unsafe { std::mem::transmute(value) }
    }

    /// Returns an iterator over all positions on the board.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::Position;
    ///
    /// // Iterate through all positions
    /// for position in Position::iter() {
    ///     println!("Position: {:?}", position);
    /// }
    /// ```
    pub fn iter() -> PositionIter {
        PositionIter::new()
    }
}

impl From<Position> for u32 {
    fn from(value: Position) -> Self {
        value as u32
    }
}

impl TryFrom<u32> for Position {
    type Error = crate::error::Error;
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        // Check if the value has bits in valid position bit patterns (non-zero when ANDed with 0x8888_8888)
        // and has exactly one bit set (valid positions have only one bit set)
        if (value & 0x8888_8888) != 0 && value.count_ones() == 1 {
            Ok(unsafe { Position::from_u32_unchecked(value) })
        } else {
            Err(crate::error::Error::Position(value))
        }
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Position::*;
        let s = match self {
            N => "N",
            NE => "NE",
            E => "E",
            SE => "SE",
            S => "S",
            SW => "SW",
            W => "W",
            NW => "NW",
        };
        write!(f, "{}", s)
    }
}

/// An iterator that yields all positions on the board in sequence.
///
/// This iterator returns positions in the order: N, NE, E, SE, S, SW, W, NW.
#[derive(Debug)]
pub struct PositionIter {
    value: u32,
}

impl PositionIter {
    /// Creates a new position iterator.
    fn new() -> Self {
        Self { value: 0x0000_0008 }
    }
}

impl Iterator for PositionIter {
    type Item = Position;
    fn next(&mut self) -> Option<Self::Item> {
        if self.value == 0 {
            None
        } else {
            let pos = unsafe { Position::from_u32_unchecked(self.value) };
            self.value <<= 4;
            Some(pos)
        }
    }
}

/// Represents a player's color in the game.
///
/// There are two colors in the game:
/// - `B` for Black
/// - `W` for White
///
/// # Examples
///
/// ```
/// use secondbest::board::Color;
///
/// let black = Color::B;
/// let white = Color::W;
///
/// // Get the opposite color
/// let opposite_of_black = black.opposite();
/// assert_eq!(opposite_of_black, Color::W);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Color {
    /// Black piece
    B,
    /// White piece
    W,
}

impl Color {
    /// Returns the opposite color.
    ///
    /// # Returns
    /// * `Color::W` if called on `Color::B`
    /// * `Color::B` if called on `Color::W`
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::Color;
    ///
    /// assert_eq!(Color::B.opposite(), Color::W);
    /// assert_eq!(Color::W.opposite(), Color::B);
    /// ```
    pub fn opposite(self) -> Self {
        use Color::*;
        match self {
            B => W,
            W => B,
        }
    }
}

impl From<bool> for Color {
    fn from(value: bool) -> Self {
        if value { Color::B } else { Color::W }
    }
}

impl From<Color> for bool {
    fn from(value: Color) -> Self {
        matches!(value, Color::B)
    }
}

impl std::fmt::Display for Color {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Color::*;
        let s = match self {
            B => "Black",
            W => "White",
        };
        write!(f, "{}", s)
    }
}

/// Represents an action that a player can perform in the game.
///
/// Actions can be either placing a new piece on the board (`Put`) or
/// moving an existing piece from one position to another (`Move`).
///
/// # Examples
///
/// ```
/// use secondbest::board::{Action, Position, Color};
///
/// // Creating a Put action (placing a black piece at position N)
/// let put_action = Action::Put(Position::N, Color::B);
///
/// // Creating a Move action (moving a piece from position N to position E)
/// let move_action = Action::Move(Position::N, Position::E);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Action {
    /// Represents placing a new piece of the specified color at the given position.
    Put(Position, Color),
    /// Represents moving a piece from one position to another.
    Move(Position, Position),
}

impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Action::Put(pos, color) => write!(f, "Put({}, {})", pos, color),
            Action::Move(from, to) => write!(f, "Move({}, {})", from, to),
        }
    }
}
