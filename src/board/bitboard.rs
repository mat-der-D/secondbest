//! Bit-based representation of the game board.
//!
//! This module provides a low-level, efficient implementation of the game board using
//! bit manipulation. The `BitBoard` struct represents the board state as a 32-bit integer,
//! where each position is encoded in 4 bits, allowing for fast operations and compact storage.
//!
//! The module includes functionality for:
//! - Placing and moving pieces
//! - Checking for valid moves
//! - Determining if a player has lined up pieces
//! - Iterating through legal actions
//!
//! This implementation serves as the foundation for the higher-level board representation
//! and game logic.

use crate::board::legal_actions::{BitLegalMoveIter, BitLegalPutIter};
use crate::error::BitBoardError;

/// A bit-based representation of the game board, using a 32-bit integer to efficiently
/// store and manipulate the board state.
///
/// ## Bit Pattern Representation
///
/// The `BitBoard` uses a 32-bit integer where each position on the board is represented
/// by 4 bits. There are 8 positions on the board (N, NE, E, SE, S, SW, W, NW), each
/// mapped to a specific bit pattern.
///
/// ### Bit Layout (32-bit integer)
///
/// ```text
/// MSB                                 LSB
/// 0000 0000 0000 0000 0000 0000 0000 0000
/// |NW| |W | |SW| |S | |SE| |E | |NE| |N |
/// ```
///
/// ### Bit Interpretation
///
/// Each 4-bit block is interpreted as follows:
/// - Only the bits above the first '0' bit (searching from LSB) are meaningful
/// - In the meaningful bits, the most significant bit indicates the piece color:
///   - '1' represents a black piece
///   - '0' represents a white piece
/// - If no '0' bit is found in a 4-bit block (i.e., 0b0111), the position is empty
/// - Note: 0b1111 is not a valid state and is not used in the implementation
///
/// ### Examples
///
/// Note: In the examples below, the pieces are listed from top to bottom, where the top piece
/// is the one visible from above (the last piece placed).
///
/// - `0b0111` (0x7): \[ \] (empty position)
/// - `0b0011` (0x3): \[White\] (one white piece)
/// - `0b1011` (0xB): \[Black\] (one black piece)
/// - `0b0001` (0x1): \[White, White\] (two white pieces)
/// - `0b1001` (0x9): \[Black, White\] (black piece on top of white piece)
/// - `0b0101` (0x5): \[White, Black\] (white piece on top of black piece)
/// - `0b1101` (0xD): \[Black, Black\] (two black pieces)
/// - `0b0000` (0x0): \[White, White, White\] (three white pieces)
/// - `0b1110` (0xE): \[Black, Black, Black\] (three black pieces)
///
/// ### Default Board State
///
/// The default board state is `0x7777_7777`, which means all positions are empty
/// (each position is 0x7 or 0b0111).
///
/// ### Common Bit Operations
///
/// - `bits & 0x8888_8888`: Check the most significant bit at each position (check for black pieces at the top)
/// - `bits & 0xEEEE_EEEE`: Check the top 3 bits at each position (detect 0b1110 pattern)
/// - `(bits << 3) & 0x8888_8888`: Check for available positions (check if top bit at each position is empty)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitBoard {
    bits: u32,
}

impl std::default::Default for BitBoard {
    fn default() -> Self {
        Self::new(0x7777_7777) // 0x7 = 0b0111
    }
}

impl std::fmt::Display for BitBoard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "BitBoard({:04b}_{:04b}_{:04b}_{:04b}_{:04b}_{:04b}_{:04b}_{:04b})",
            (self.bits >> 28) & 0xF,
            (self.bits >> 24) & 0xF,
            (self.bits >> 20) & 0xF,
            (self.bits >> 16) & 0xF,
            (self.bits >> 12) & 0xF,
            (self.bits >> 8) & 0xF,
            (self.bits >> 4) & 0xF,
            self.bits & 0xF
        )
    }
}

impl BitBoard {
    /// Creates a new BitBoard with the specified bit pattern.
    ///
    /// # Arguments
    /// * `bits` - The bit pattern to initialize the board with
    ///
    /// # Returns
    /// * A new BitBoard instance
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::BitBoard;
    ///
    /// // Create a BitBoard with a specific bit pattern
    /// let board = BitBoard::new(0x7777_7777);
    /// assert_eq!(board.bits(), 0x7777_7777);
    /// ```
    pub fn new(bits: u32) -> Self {
        Self { bits }
    }

    /// Returns the raw bit pattern of the board.
    ///
    /// # Returns
    /// * The 32-bit integer representing the board state
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::BitBoard;
    ///
    /// // Create a BitBoard and access its bits
    /// let board = BitBoard::new(0x1234_5678);
    /// assert_eq!(board.bits(), 0x1234_5678);
    /// ```
    pub fn bits(&self) -> u32 {
        self.bits
    }

    /// Checks if the bitboard has a valid bit pattern.
    ///
    /// A valid bitboard must not have 4 consecutive hot bits in any position,
    /// as this would violate the bit pattern specification for board representation.
    ///
    /// # Returns
    /// * `true` if the bitboard has a valid bit pattern
    /// * `false` if the bitboard contains an invalid pattern
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::BitBoard;
    ///
    /// // Default board should be valid
    /// let board = BitBoard::default();
    /// assert!(board.has_valid_bits());
    ///
    /// // A board with 4 consecutive bits (0xF) should be invalid
    /// let invalid_board = BitBoard::new(0x0000_000F);
    /// assert!(!invalid_board.has_valid_bits());
    /// ```
    pub fn has_valid_bits(&self) -> bool {
        fn _contains_4_consecutive_hot_bits(mut bits: u32) -> bool {
            bits = bits & (bits >> 1);
            bits = bits & (bits >> 2);
            bits != 0
        }

        !_contains_4_consecutive_hot_bits(self.bits & 0xF0F0_F0F0) // 0xF = 0b1111
            && !_contains_4_consecutive_hot_bits(self.bits & 0x0F0F0F0F) // 0xF = 0b1111
    }

    /// Swaps the colors of all pieces on the board.
    ///
    /// This operation transforms all black pieces to white and vice versa.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Add a black piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    /// // Add a white piece at position E
    /// board.put_unchecked(Position::E as u32, false);
    ///
    /// // Count pieces of each color before swap
    /// let black_before = board.count_pieces(true);
    /// let white_before = board.count_pieces(false);
    ///
    /// // Swap colors
    /// board.swap_colors();
    ///
    /// // Check that the counts are reversed
    /// assert_eq!(board.count_pieces(true), white_before);
    /// assert_eq!(board.count_pieces(false), black_before);
    /// ```
    pub fn swap_colors(&mut self) {
        self.bits = !self.bits - 0x1111_1111;
    }

    /// Flips the board horizontally.
    ///
    /// This operation mirrors the board along the vertical axis.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Add a piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Save original board state
    /// let original_bits = board.bits();
    ///
    /// // Flip the board twice (should return to original state)
    /// board.flip();
    /// board.flip();
    ///
    /// // Check that the board is back to its original state
    /// assert_eq!(board.bits(), original_bits);
    /// ```
    pub fn flip(&mut self) {
        self.bits = self.bits.swap_bytes();
        self.bits = ((self.bits & 0xF0F0_F0F0) >> 4) | ((self.bits & 0x0F0F_0F0F) << 4);
    }

    /// Rotates the board clockwise by n positions.
    ///
    /// # Arguments
    /// * `n` - The number of positions to rotate
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Add a piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Save original board state
    /// let original_bits = board.bits();
    ///
    /// // Rotate the board by 8 positions (full circle, should return to original state)
    /// board.rotate_clockwise(8);
    ///
    /// // Check that the board is back to its original state
    /// assert_eq!(board.bits(), original_bits);
    /// ```
    pub fn rotate_clockwise(&mut self, n: u32) {
        self.bits = self.bits.rotate_left(4 * n);
    }

    /// Rotates the board counterclockwise by n positions.
    ///
    /// # Arguments
    /// * `n` - The number of positions to rotate
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Add a piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Save original board state
    /// let original_bits = board.bits();
    ///
    /// // Rotate the board by 8 positions counterclockwise (full circle, should return to original state)
    /// board.rotate_counterclockwise(8);
    ///
    /// // Check that the board is back to its original state
    /// assert_eq!(board.bits(), original_bits);
    /// ```
    pub fn rotate_counterclockwise(&mut self, n: u32) {
        self.bits = self.bits.rotate_right(4 * n);
    }

    /// Counts the number of pieces of the specified color.
    ///
    /// # Arguments
    /// * `color` - The color of the pieces to count (as boolean)
    ///
    /// # Returns
    /// * The number of pieces of the specified color
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Initially, the board is empty
    /// assert_eq!(board.count_pieces(true), 0);
    /// assert_eq!(board.count_pieces(false), 0);
    ///
    /// // Add some pieces
    /// board.put_unchecked(Position::N as u32, true);  // Black piece at N
    /// board.put_unchecked(Position::E as u32, false); // White piece at E
    /// board.put_unchecked(Position::S as u32, true);  // Black piece at S
    ///
    /// // Check counts
    /// assert_eq!(board.count_pieces(true), 2);  // Two black pieces
    /// assert_eq!(board.count_pieces(false), 1); // One white piece
    /// ```
    pub fn count_pieces(&self, color: bool) -> u32 {
        if color {
            (self.bits + 0x1111_1111).count_ones() - 8
        } else {
            self.bits.count_zeros() - 8
        }
    }

    /// Gets all pieces at the specified position.
    ///
    /// # Arguments
    /// * `pos` - The position to get the pieces from (bit representation)
    ///
    /// # Returns
    /// * A vector of colors of the pieces at the specified position (as booleans)
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Initially, the position is empty
    /// assert!(board.get_pieces_at(Position::N as u32).is_empty());
    ///
    /// // Add a black piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    /// assert_eq!(board.get_pieces_at(Position::N as u32), vec![true]);
    ///
    /// // Add a white piece on top
    /// board.put_unchecked(Position::N as u32, false);
    /// assert_eq!(board.get_pieces_at(Position::N as u32), vec![true, false]);
    /// ```
    pub fn get_pieces_at(&self, pos: u32) -> Vec<bool> {
        let mut pieces = Vec::new();
        let mut cursor = pos >> 3;
        let mut is_piece = false;
        for _ in 0..4 {
            if is_piece {
                pieces.push(self.bits & cursor != 0);
            }
            is_piece |= self.bits & cursor == 0;
            cursor <<= 1;
        }
        pieces
    }

    /// Checks if the specified color has achieved a winning condition.
    ///
    /// A player wins if either:
    /// 1. They have 3 pieces of their color stacked in a single position
    /// 2. They have pieces at the top of 4 consecutive positions
    ///
    /// Note: This method only checks the board state and does not consider:
    /// - Whether "second best" declarations are still available
    /// - Which player made the last move (for simultaneous wins)
    /// - Whether the player has legal moves available
    ///
    /// # Arguments
    /// * `color` - The color to check (as boolean)
    ///
    /// # Returns
    /// * `true` if the specified color has won
    /// * `false` otherwise
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Initially, no player has won
    /// assert!(!board.lines_up(true));
    ///
    /// // Creating a vertical line-up (3 black pieces in a stack)
    /// board.put_unchecked(Position::N as u32, true);
    /// board.put_unchecked(Position::N as u32, true);
    /// board.put_unchecked(Position::N as u32, true);
    /// assert!(board.lines_up(true));
    /// ```
    pub fn lines_up(&self, color: bool) -> bool {
        let bits = if color {
            self.bits
        } else {
            !self.bits - 0x1111_1111
        };

        // Lines up vertically
        let top3 = bits & 0xEEEE_EEEE; // 0xE = 0b1110
        if top3 & (top3 >> 1) & (top3 >> 2) != 0 {
            return true;
        }

        // Lines up horizontally
        let top1 = bits & 0x8888_8888; // 0x8 = 0b1000
        if top1 & top1.rotate_left(4) & top1.rotate_left(8) & top1.rotate_left(12) != 0 {
            return true;
        }

        false
    }

    /// Places a piece of the specified color at the specified position.
    ///
    /// # Arguments
    /// * `pos` - The position to place the piece (bit representation)
    /// * `color` - The color of the piece to place (as boolean)
    ///
    /// # Returns
    /// * `Ok(())` - If the piece was successfully placed
    /// * `Err(BitBoardError)` - If the piece could not be placed
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Place a black piece at position N
    /// assert!(board.put(Position::N as u32, true).is_ok());
    /// assert_eq!(board.get_pieces_at(Position::N as u32), vec![true]);
    ///
    /// // Place a white piece on top
    /// assert!(board.put(Position::N as u32, false).is_ok());
    /// assert_eq!(board.get_pieces_at(Position::N as u32), vec![true, false]);
    ///
    /// // Place a black piece on top
    /// assert!(board.put(Position::N as u32, true).is_ok());
    /// assert_eq!(board.get_pieces_at(Position::N as u32), vec![true, false, true]);
    ///
    /// // Trying to place a fourth piece should fail
    /// assert!(board.put(Position::N as u32, false).is_err());
    /// ```
    pub fn put(&mut self, pos: u32, color: bool) -> Result<(), BitBoardError> {
        if self.bits & (pos >> 3) == 0 {
            return Err(BitBoardError::PositionOccupied(pos));
        }

        self.put_unchecked(pos, color);
        Ok(())
    }

    /// Places a piece of the specified color at the specified position without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid bit pattern
    /// if used with unnatural operations (e.g., placing a piece on a stack that already has 3 pieces).
    /// However, it provides faster execution by skipping checks.
    ///
    /// # Arguments
    /// * `pos` - The position to place the piece (bit representation)
    /// * `color` - The color of the piece to place (as boolean)
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Place a black piece at position N without validation
    /// board.put_unchecked(Position::N as u32, true);
    /// assert_eq!(board.get_pieces_at(Position::N as u32), vec![true]);
    /// ```
    pub fn put_unchecked(&mut self, pos: u32, color: bool) {
        let mask_stack = pos | (pos >> 1) | (pos >> 2);
        let mask_others = !(mask_stack | (pos >> 3));
        self.bits = ((self.bits & mask_stack) >> 1) | (self.bits & mask_others);
        if color {
            self.bits |= pos;
        }
    }

    /// Removes a piece from the specified position.
    ///
    /// # Arguments
    /// * `pos` - The position to remove the piece from (bit representation)
    ///
    /// # Returns
    /// * `Ok(bool)` - The color of the removed piece (as boolean)
    /// * `Err(BitBoardError)` - If the piece could not be removed
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Place a black piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Remove the piece
    /// let removed = board.remove(Position::N as u32);
    /// assert!(removed.is_ok());
    /// assert_eq!(removed.unwrap(), true); // Should be black (true)
    /// assert!(board.get_pieces_at(Position::N as u32).is_empty());
    ///
    /// // Trying to remove from an empty position should fail
    /// assert!(board.remove(Position::N as u32).is_err());
    /// ```
    pub fn remove(&mut self, pos: u32) -> Result<bool, BitBoardError> {
        if pos & (self.bits << 1) & (self.bits << 2) & (self.bits << 3) != 0 {
            return Err(BitBoardError::EmptyPosition(pos));
        }

        let removed = self.remove_unchecked(pos);
        Ok(removed)
    }

    /// Removes a piece from the specified position without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid bit pattern
    /// if used with unnatural operations (e.g., removing a piece from a position with no pieces).
    /// However, it provides faster execution by skipping checks.
    ///
    /// # Arguments
    /// * `pos` - The position to remove the piece from (bit representation)
    ///
    /// # Returns
    /// * The color of the removed piece (as boolean)
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Place a black piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Remove the piece without validation
    /// let removed = board.remove_unchecked(Position::N as u32);
    /// assert_eq!(removed, true); // Should be black (true)
    /// assert!(board.get_pieces_at(Position::N as u32).is_empty());
    /// ```
    pub fn remove_unchecked(&mut self, pos: u32) -> bool {
        let mask_stack = (pos >> 1) | (pos >> 2) | (pos >> 3);
        let mask_others = !(mask_stack | pos);
        let removed = self.bits & pos;
        self.bits = ((self.bits & mask_stack) << 1) | (pos >> 3) | self.bits & mask_others;
        removed != 0
    }

    /// Moves a piece from one position to another.
    ///
    /// # Arguments
    /// * `from` - The source position (bit representation)
    /// * `to` - The destination position (bit representation)
    ///
    /// # Returns
    /// * `Ok(())` - If the piece was successfully moved
    /// * `Err(BitBoardError)` - If the piece could not be moved
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Place a black piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Move the piece to position E
    /// assert!(board.move_(Position::N as u32, Position::E as u32).is_ok());
    /// assert!(board.get_pieces_at(Position::N as u32).is_empty());
    /// assert_eq!(board.get_pieces_at(Position::E as u32), vec![true]);
    ///
    /// // Trying to move from an empty position should fail
    /// assert!(board.move_(Position::N as u32, Position::S as u32).is_err());
    /// ```
    pub fn move_(&mut self, from: u32, to: u32) -> Result<(), BitBoardError> {
        let removed = self
            .remove(from)
            .map_err(|_| BitBoardError::InvalidMove { from, to })?;
        self.put(to, removed)
            .map_err(|_| BitBoardError::InvalidMove { from, to })
    }

    /// Moves a piece from one position to another without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid bit pattern
    /// if used with unnatural operations (e.g., moving from a position with no pieces or
    /// moving to a position that already has 3 pieces). However, it provides faster execution
    /// by skipping checks.
    ///
    /// # Arguments
    /// * `from` - The source position (bit representation)
    /// * `to` - The destination position (bit representation)
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // Place a black piece at position N
    /// board.put_unchecked(Position::N as u32, true);
    ///
    /// // Move the piece to position E without validation
    /// board.move_unchecked(Position::N as u32, Position::E as u32);
    /// assert!(board.get_pieces_at(Position::N as u32).is_empty());
    /// assert_eq!(board.get_pieces_at(Position::E as u32), vec![true]);
    /// ```
    pub fn move_unchecked(&mut self, from: u32, to: u32) {
        let removed = self.remove_unchecked(from);
        self.put_unchecked(to, removed);
    }

    /// Returns an iterator over all legal put actions for the specified color.
    ///
    /// # Arguments
    /// * `color` - The color of the player (as boolean)
    ///
    /// # Returns
    /// * An iterator that yields all legal put positions for the specified color
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let board = BitBoard::default();
    /// // Get legal put positions for black pieces
    /// let legal_puts: Vec<(u32, bool)> = board.legal_put_iter(true).collect();
    ///
    /// // On an empty board, we should have 8 possible positions
    /// assert_eq!(legal_puts.len(), 8);
    ///
    /// // All actions should be for black pieces (true)
    /// for (_, color) in legal_puts {
    ///     assert_eq!(color, true);
    /// }
    /// ```
    pub fn legal_put_iter(&self, color: bool) -> BitLegalPutIter {
        BitLegalPutIter::new(*self, color)
    }

    /// Returns an iterator over all legal move actions for the specified color.
    ///
    /// # Arguments
    /// * `color` - The color of the player (as boolean)
    ///
    /// # Returns
    /// * An iterator that yields all legal move positions for the specified color
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{BitBoard, Position};
    /// use secondbest::prelude::*;
    ///
    /// let mut board = BitBoard::default();
    /// // On an empty board, there should be no legal moves
    /// let legal_moves: Vec<(u32, u32)> = board.legal_move_iter(true).collect();
    /// assert_eq!(legal_moves.len(), 0);
    ///
    /// // Add pieces and verify moves become available
    /// board.put_unchecked(Position::N as u32, true);
    /// let legal_moves: Vec<(u32, u32)> = board.legal_move_iter(true).collect();
    /// assert!(!legal_moves.is_empty());
    /// ```
    pub fn legal_move_iter(&self, color: bool) -> BitLegalMoveIter {
        BitLegalMoveIter::new(*self, color)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::prelude::*;

    // テスト用に簡易的なボード初期化マクロを定義
    macro_rules! test_board {
        ($(
            $pos:ident: $($color:expr),*
        );* $(;)?) => {{
            let mut board = BitBoard::default();
            $(
                $(
                    board.put_unchecked(Position::$pos as u32, $color);
                )*
            )*
            board
        }};
    }

    #[test]
    fn test_new() {
        // Check if a board is created with the specified bit pattern
        let board = BitBoard::new(0x1234_5678);
        assert_eq!(board.bits(), 0x1234_5678);

        // Check if default value is correct
        let default_board = BitBoard::default();
        assert_eq!(default_board.bits(), 0x7777_7777);
    }

    #[test]
    fn test_bits() {
        // Check if internal bit pattern is correctly retrieved
        let board = BitBoard::new(0x1234_5678);
        assert_eq!(board.bits(), 0x1234_5678);

        // Check if value is correctly updated after bit operations
        let mut board = BitBoard::default();
        board.put_unchecked(Position::N as u32, true);
        assert_ne!(board.bits(), 0x7777_7777); // Should be different from default value
    }

    #[test]
    fn test_has_valid_bits() {
        // Check if true is returned for valid bit pattern
        let board = BitBoard::default();
        assert!(
            board.has_valid_bits(),
            "Default bit pattern should be valid"
        );

        // 0x1111_1111 is actually a valid bit pattern
        let valid_board = BitBoard::new(0x1111_1111);
        assert!(
            valid_board.has_valid_bits(),
            "0x1111_1111 is a valid pattern"
        );

        // Use a more clearly invalid bit pattern
        let invalid_board = BitBoard::new(0x0000_000F); // 0xF = 0b1111 (4 consecutive bits)
        assert!(
            !invalid_board.has_valid_bits(),
            "0x0000_000F should be an invalid pattern"
        );
    }

    #[test]
    fn test_swap_colors() {
        let mut board = test_board! {
            N: true;
            E: false;
            S: true
        };
        let original_board = board;
        let original_black_count = board.count_pieces(true);
        let original_white_count = board.count_pieces(false);

        board.swap_colors();

        // Check if colors are swapped
        assert_eq!(board.count_pieces(true), original_white_count);
        assert_eq!(board.count_pieces(false), original_black_count);

        // Check if all colors are inverted
        board.swap_colors();
        assert_eq!(board.count_pieces(true), original_black_count);
        assert_eq!(board.count_pieces(false), original_white_count);

        assert_eq!(board, original_board);
    }

    #[test]
    fn test_count_pieces() {
        // Check if empty board returns 0
        let board = BitBoard::default();
        assert_eq!(
            board.count_pieces(true),
            0,
            "Empty board should have no black pieces"
        );
        assert_eq!(
            board.count_pieces(false),
            0,
            "Empty board should have no white pieces"
        );

        // Accurate count for complex board layout
        let board = test_board! {
            N: true;
            E: false;
            S: true
        };
        assert_eq!(board.count_pieces(true), 2, "Should have 2 black pieces");
        assert_eq!(board.count_pieces(false), 1, "Should have 1 white piece");
    }

    #[test]
    fn test_get_pieces_at() {
        let board = BitBoard::default();

        // Check if empty position returns empty array
        assert!(
            board.get_pieces_at(Position::N as u32).is_empty(),
            "Empty position should have no pieces"
        );

        // Check if order is correct for multiple pieces
        let board = test_board! {
            N: true, true, false
        };
        let pieces = board.get_pieces_at(Position::N as u32);
        assert_eq!(
            pieces,
            vec![true, true, false],
            "Position N should have pieces in order [true, true, false] from bottom"
        );
    }

    #[test]
    fn test_lines_up() {
        // Check win condition with 3 vertical black pieces
        let board = test_board! {
            N: true, true, true
        };
        assert!(
            board.lines_up(true),
            "Three vertical black pieces should satisfy win condition"
        );
        assert!(
            !board.lines_up(false),
            "White pieces should not satisfy win condition"
        );

        // Check win condition with 4 horizontal consecutive black pieces
        // Using consecutive positions like N, NE, E, SE
        let board = test_board! {
            N: true;
            NE: true;
            E: true;
            SE: true
        };
        assert!(
            board.lines_up(true),
            "Four consecutive black pieces should satisfy win condition"
        );

        // Pattern that doesn't satisfy win condition
        let board = test_board! {
            N: true;
            S: true
        };
        assert!(
            !board.lines_up(true),
            "Non-consecutive pieces should not satisfy win condition"
        );
    }

    #[test]
    fn test_put() {
        let mut board = BitBoard::default();

        // Check if a piece can be placed in an empty position
        assert!(board.put(Position::N as u32, true).is_ok());
        assert_eq!(board.get_pieces_at(Position::N as u32), vec![true]);

        // Check if error occurs when placing in a full position
        let mut board = test_board! {
            N: true, true, true
        };
        assert!(board.put(Position::N as u32, false).is_err());
    }

    #[test]
    fn test_put_unchecked() {
        let mut board = BitBoard::default();

        // Check if a piece can be placed without validation
        board.put_unchecked(Position::N as u32, true);
        assert_eq!(board.get_pieces_at(Position::N as u32), vec![true]);

        // Check if bit pattern is correctly updated
        let old_bits = board.bits();
        board.put_unchecked(Position::E as u32, false);
        assert_ne!(board.bits(), old_bits);
    }

    #[test]
    fn test_remove() {
        let mut board = test_board! {
            N: true
        };

        // Remove piece from top and check if color is correct
        let result = board.remove(Position::N as u32);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), true);
        assert!(board.get_pieces_at(Position::N as u32).is_empty());

        // Check if error occurs when removing from empty position
        assert!(board.remove(Position::N as u32).is_err());
    }

    #[test]
    fn test_remove_unchecked() {
        let mut board = test_board! {
            N: true
        };

        // Check if a piece can be removed without validation
        let removed = board.remove_unchecked(Position::N as u32);
        assert_eq!(removed, true);
        assert!(board.get_pieces_at(Position::N as u32).is_empty());
    }

    #[test]
    fn test_move() {
        let mut board = test_board! {
            N: true
        };

        // Check if a legal move succeeds
        assert!(board.move_(Position::N as u32, Position::E as u32).is_ok());
        assert!(board.get_pieces_at(Position::N as u32).is_empty());
        assert_eq!(board.get_pieces_at(Position::E as u32), vec![true]);

        // Check if an illegal move fails
        assert!(board.move_(Position::N as u32, Position::S as u32).is_err()); // N is empty
    }

    #[test]
    fn test_move_unchecked() {
        let mut board = test_board! {
            N: true
        };

        // Check if a piece can be moved without validation
        board.move_unchecked(Position::N as u32, Position::E as u32);
        assert!(board.get_pieces_at(Position::N as u32).is_empty());
        assert_eq!(board.get_pieces_at(Position::E as u32), vec![true]);

        // Check if bit pattern is correct after move
        let expected = test_board! {
            E: true
        };
        assert_eq!(board.bits(), expected.bits());
    }

    #[test]
    fn test_rotate_clockwise() {
        let mut board = test_board! {
            N: true;
            E: false;
            S: true
        };

        // Save the original board
        let original = board;

        // Rotate 8 times (full 360 degrees) and verify it returns to the original state
        for _ in 0..8 {
            board.rotate_clockwise(1);
        }

        assert_eq!(
            original, board,
            "Rotating 8 times should return to the original board state"
        );
    }

    #[test]
    fn test_rotate_counterclockwise() {
        let mut board = test_board! {
            N: true;
            E: false;
            S: true
        };

        // Save the original board
        let original = board;

        // Rotate 8 times (full 360 degrees) and verify it returns to the original state
        for _ in 0..8 {
            board.rotate_counterclockwise(1);
        }

        assert_eq!(
            original, board,
            "Rotating 8 times counterclockwise should return to the original board state"
        );
    }

    #[test]
    fn test_flip() {
        let mut board = test_board! {
            N: true;
            E: false;
            S: true
        };

        // Save the original board
        let original = board;

        // Flip twice and verify it returns to the original state
        board.flip();
        board.flip();

        assert_eq!(
            original, board,
            "Flipping twice should return to the original board state"
        );
    }
}
