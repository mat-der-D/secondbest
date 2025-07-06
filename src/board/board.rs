//! High-level representation of the game board.
//!
//! This module provides a user-friendly API for interacting with the game board,
//! abstracting away the bit-level operations of the underlying BitBoard implementation.
//! It offers methods for placing and moving pieces, checking game state, and iterating
//! through legal actions.
//!
//! The `Board` struct serves as the main interface for game logic, providing methods that
//! operate on logical positions rather than bit patterns, making the code more readable
//! and maintainable.

use crate::board::bitboard::BitBoard;
use crate::board::legal_actions::{LegalActionIter, LegalMoveIter, LegalPutIter};
use crate::board::types::{Action, Color, Position};
use crate::error::BoardError;

/// A high-level representation of the game board that wraps the BitBoard implementation.
///
/// This struct provides a more user-friendly API for interacting with the game board,
/// abstracting away the bit-level operations of the underlying BitBoard.
///
/// # Examples
///
/// ```
/// use secondbest::board::Board;
///
/// // Create a new empty board
/// let board = Board::default();
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Board {
    inner: BitBoard,
}

impl Board {
    /// Returns a reference to the inner BitBoard.
    ///
    /// # Returns
    /// * A reference to the inner BitBoard
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, BitBoard};
    ///
    /// let board = Board::default();
    /// let bit_board = board.inner();
    /// ```
    pub fn inner(&self) -> &BitBoard {
        &self.inner
    }

    /// Returns a mutable reference to the inner BitBoard.
    ///
    /// # Returns
    /// * A mutable reference to the inner BitBoard
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, BitBoard};
    ///
    /// let mut board = Board::default();
    /// let bit_board_mut = board.inner_mut();
    /// ```
    pub fn inner_mut(&mut self) -> &mut BitBoard {
        &mut self.inner
    }

    /// Creates a new Board from an inner BitBoard.
    ///
    /// # Arguments
    /// * `inner` - The BitBoard to use as the inner representation
    ///
    /// # Returns
    /// * A new Board instance with the specified inner BitBoard
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, BitBoard};
    ///
    /// let bit_board = BitBoard::default();
    /// let board = Board::from_inner(bit_board);
    /// ```
    pub fn from_inner(inner: BitBoard) -> Self {
        Self { inner }
    }
}

impl Board {
    /// Checks if the board has a valid internal state.
    ///
    /// Note that using unchecked methods like `move_unchecked` may result in an invalid board state.
    ///
    /// # Returns
    /// * `true` if the board has a valid internal state
    /// * `false` otherwise
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::Board;
    ///
    /// let board = Board::default();
    /// assert!(board.is_valid());
    /// ```
    pub fn is_valid(&self) -> bool {
        self.inner.has_valid_bits()
    }

    /// Counts the number of pieces of the specified color.
    ///
    /// # Arguments
    /// * `color` - The color of the pieces to count
    ///
    /// # Returns
    /// * The number of pieces of the specified color
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Initially, the board is empty
    /// assert_eq!(board.count_pieces(Color::B), 0);
    ///
    /// // Add some pieces
    /// board.put(Position::N, Color::B).unwrap();
    /// board.put(Position::S, Color::B).unwrap();
    /// assert_eq!(board.count_pieces(Color::B), 2);
    /// ```
    pub fn count_pieces(&self, color: Color) -> u32 {
        self.inner.count_pieces(color.into())
    }

    /// Gets all pieces at the specified position.
    ///
    /// # Arguments
    /// * `pos` - The position to get the pieces from
    ///
    /// # Returns
    /// * A vector of colors of the pieces at the specified position
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Initially, the position is empty
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    ///
    /// // Add a piece
    /// board.put(Position::N, Color::B).unwrap();
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);
    ///
    /// // Add another piece on top
    /// board.put(Position::N, Color::W).unwrap();
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B, Color::W]);
    /// ```
    pub fn get_pieces_at(&self, pos: Position) -> Vec<Color> {
        let pieces = self.inner.get_pieces_at(pos.into());
        pieces.into_iter().map(Color::from).collect()
    }

    /// Checks if the specified color has achieved a winning condition.
    ///
    /// A player wins when:
    /// - They have three pieces in a single stack (vertical line-up)
    /// - They have their pieces at the top of four consecutive positions (horizontal line-up)
    ///
    /// Note: This method only checks the board state and does not consider:
    /// - Whether "second best" declarations are still available
    /// - Which player made the last move (for simultaneous wins)
    /// - Whether the player has legal moves available
    ///
    /// # Arguments
    /// * `color` - The color to check for a winning condition
    ///
    /// # Returns
    /// * `true` if the specified color has won
    /// * `false` otherwise
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Initially, no player has won
    /// assert!(!board.lines_up(Color::B));
    ///
    /// // Creating a vertical line-up (3 pieces in a stack)
    /// board.put(Position::N, Color::B).unwrap();
    /// board.put(Position::N, Color::B).unwrap();
    /// board.put(Position::N, Color::B).unwrap();
    /// assert!(board.lines_up(Color::B));
    /// ```
    pub fn lines_up(&self, color: Color) -> bool {
        self.inner.lines_up(color.into())
    }

    /// Applies an action to the board.
    ///
    /// # Arguments
    /// * `action` - The action to apply (placement or movement)
    ///
    /// # Returns
    /// * `Ok(())` - If the action was successfully applied
    /// * `Err(BoardError)` - If the action could not be applied
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color, Action};
    ///
    /// let mut board = Board::default();
    /// // Place a piece
    /// assert!(board.apply(Action::Put(Position::N, Color::B)).is_ok());
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);
    ///
    /// // Move the piece
    /// assert!(board.apply(Action::Move(Position::N, Position::E)).is_ok());
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    /// assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);
    /// ```
    pub fn apply(&mut self, action: Action) -> Result<(), BoardError> {
        use Action::*;
        match action {
            Put(pos, color) => self.put(pos, color),
            Move(from, to) => self.move_(from, to),
        }
    }

    /// Applies an action to the board without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid board state
    /// if used with unnatural operations (e.g., placing a piece on a stack that already has 3 pieces,
    /// moving from a position with no pieces, or moving to a position that already has 3 pieces).
    /// However, it provides faster execution by skipping checks.
    ///
    /// # Arguments
    /// * `action` - The action to apply (placement or movement)
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color, Action};
    ///
    /// let mut board = Board::default();
    /// // Place a piece without validation
    /// board.apply_unchecked(Action::Put(Position::N, Color::B));
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);
    ///
    /// // Move the piece without validation
    /// board.apply_unchecked(Action::Move(Position::N, Position::E));
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    /// assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);
    /// ```
    pub fn apply_unchecked(&mut self, action: Action) {
        use Action::*;
        match action {
            Put(pos, color) => self.put_unchecked(pos, color),
            Move(from, to) => self.move_unchecked(from, to),
        }
    }

    /// Places a piece of the specified color at the specified position.
    ///
    /// # Arguments
    /// * `pos` - The position to place the piece
    /// * `color` - The color of the piece to place
    ///
    /// # Returns
    /// * `Ok(())` - If the piece was successfully placed
    /// * `Err(BoardError)` - If the piece could not be placed
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Place a piece
    /// assert!(board.put(Position::N, Color::B).is_ok());
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);
    ///
    /// // Place another piece on top
    /// assert!(board.put(Position::N, Color::W).is_ok());
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B, Color::W]);
    ///
    /// // Try to place too many pieces (should fail after 3)
    /// board.put(Position::N, Color::B).unwrap();
    /// assert!(board.put(Position::N, Color::W).is_err());
    /// ```
    pub fn put(&mut self, pos: Position, color: Color) -> Result<(), BoardError> {
        self.inner
            .put(pos.into(), color.into())
            .map_err(|_| BoardError::PositionOccupied(pos))
    }

    /// Places a piece of the specified color at the specified position without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid board state
    /// if used with unnatural operations (e.g., placing a piece on a stack that already has 3 pieces).
    /// However, it provides faster execution by skipping checks.
    ///
    /// # Arguments
    /// * `pos` - The position to place the piece
    /// * `color` - The color of the piece to place
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Place a piece without validation
    /// board.put_unchecked(Position::N, Color::B);
    /// assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);
    /// ```
    pub fn put_unchecked(&mut self, pos: Position, color: Color) {
        self.inner.put_unchecked(pos.into(), color.into());
    }

    /// Removes a piece from the specified position.
    ///
    /// # Arguments
    /// * `pos` - The position to remove the piece from
    ///
    /// # Returns
    /// * `Ok(Color)` - The color of the removed piece
    /// * `Err(BoardError)` - If the piece could not be removed
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Place a piece
    /// board.put(Position::N, Color::B).unwrap();
    ///
    /// // Remove the piece
    /// let removed = board.remove(Position::N);
    /// assert!(removed.is_ok());
    /// assert_eq!(removed.unwrap(), Color::B);
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    ///
    /// // Try to remove from an empty position
    /// assert!(board.remove(Position::N).is_err());
    /// ```
    pub fn remove(&mut self, pos: Position) -> Result<Color, BoardError> {
        let color = self
            .inner
            .remove(pos.into())
            .map_err(|_| BoardError::EmptyPosition(pos))?;
        Ok(color.into())
    }

    /// Removes a piece from the specified position without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid board state
    /// if used with unnatural operations (e.g., removing a piece from a position with no pieces).
    /// However, it provides faster execution by skipping checks.
    ///
    /// # Arguments
    /// * `pos` - The position to remove the piece from
    ///
    /// # Returns
    /// * The color of the removed piece
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Place a piece
    /// board.put(Position::N, Color::B).unwrap();
    ///
    /// // Remove the piece without validation
    /// let removed = board.remove_unchecked(Position::N);
    /// assert_eq!(removed, Color::B);
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    /// ```
    pub fn remove_unchecked(&mut self, pos: Position) -> Color {
        self.inner.remove_unchecked(pos.into()).into()
    }

    /// Moves a piece from one position to another.
    ///
    /// # Arguments
    /// * `from` - The source position
    /// * `to` - The destination position
    ///
    /// # Returns
    /// * `Ok(())` - If the piece was successfully moved
    /// * `Err(BoardError)` - If the piece could not be moved
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Place a piece
    /// board.put(Position::N, Color::B).unwrap();
    ///
    /// // Move the piece
    /// assert!(board.move_(Position::N, Position::E).is_ok());
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    /// assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);
    ///
    /// // Try to move from an empty position
    /// assert!(board.move_(Position::N, Position::S).is_err());
    /// ```
    pub fn move_(&mut self, from: Position, to: Position) -> Result<(), BoardError> {
        self.inner
            .move_(from.into(), to.into())
            .map_err(|_| BoardError::InvalidMove { from, to })
    }

    /// Moves a piece from one position to another without validation.
    ///
    /// Note: This method performs no validation, which may lead to an invalid board state
    /// if used with unnatural operations (e.g., moving from a position with no pieces or
    /// moving to a position that already has 3 pieces). However, it provides faster execution
    /// by skipping checks.
    ///
    /// # Arguments
    /// * `from` - The source position
    /// * `to` - The destination position
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color};
    ///
    /// let mut board = Board::default();
    /// // Place a piece
    /// board.put(Position::N, Color::B).unwrap();
    ///
    /// // Move the piece without validation
    /// board.move_unchecked(Position::N, Position::E);
    /// assert!(board.get_pieces_at(Position::N).is_empty());
    /// assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);
    /// ```
    pub fn move_unchecked(&mut self, from: Position, to: Position) {
        self.inner.move_unchecked(from.into(), to.into());
    }

    /// Returns an iterator over all legal actions.
    ///
    /// # Arguments
    /// * `color` - The color of the player
    ///
    /// # Returns
    /// * An iterator that yields all legal actions (puts or moves)
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::board::{Board, Position, Color, Action};
    ///
    /// let board = Board::default();
    /// // Create a legal action iterator for black pieces
    /// let actions: Vec<Action> = board.legal_action_iter(Color::B).collect();
    /// // On an empty board, we should have 8 possible positions to place pieces
    /// assert_eq!(actions.len(), 8);
    ///
    /// // All actions should be Put actions
    /// for action in actions {
    ///     match action {
    ///         Action::Put(_, color) => assert_eq!(color, Color::B),
    ///         _ => panic!("Expected only Put actions on an empty board!"),
    ///     }
    /// }
    /// ```
    pub fn legal_action_iter(&self, color: Color) -> LegalActionIter {
        if self.count_pieces(color) < 8 {
            let bit_iter = self.inner.legal_put_iter(color.into());
            LegalActionIter::with_put_iter(LegalPutIter::new(bit_iter))
        } else {
            let bit_iter = self.inner.legal_move_iter(color.into());
            LegalActionIter::with_move_iter(LegalMoveIter::new(bit_iter))
        }
    }
}

impl std::fmt::Display for Board {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn _pos_to_str(pos: Position) -> &'static str {
            use Position::*;
            match pos {
                N => "N ",
                NE => "NE",
                E => "E ",
                SE => "SE",
                S => "S ",
                SW => "SW",
                W => "W ",
                NW => "NW",
            }
        }

        fn _color_to_str(color: Color) -> &'static str {
            use Color::*;
            match color {
                B => "B",
                W => "W",
            }
        }

        if !self.is_valid() {
            return write!(f, "Invalid internal state");
        }

        for pos in Position::iter() {
            let pieces = self.get_pieces_at(pos);
            let pieces_str: String = pieces.into_iter().map(_color_to_str).collect();
            writeln!(f, "{}: {}", _pos_to_str(pos), pieces_str)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // Define a macro for easy board initialization in tests
    macro_rules! test_board {
        ($(
            $pos:ident: $($color:ident),*
        );* $(;)?) => {{
            let mut board = Board::default();
            $(
                $(
                    board.put_unchecked(Position::$pos, Color::$color);
                )*
            )*
            board
        }};
    }

    #[test]
    fn test_is_valid() {
        // Test if default board is valid
        let board = Board::default();
        assert!(board.is_valid(), "Default board should be valid");

        // Create an invalid board with invalid bit pattern
        let invalid_board = Board {
            inner: BitBoard::new(0xFFFF_FFFF), // Invalid pattern
        };
        // Bit pattern 0xFFFF_FFFF is invalid (all bits set)
        assert!(
            !invalid_board.is_valid(),
            "Bit pattern 0xFFFF_FFFF should be invalid"
        );
    }

    #[test]
    fn test_count_pieces() {
        // Check if empty board returns 0
        let board = Board::default();
        assert_eq!(
            board.count_pieces(Color::B),
            0,
            "Empty board should have no black pieces"
        );
        assert_eq!(
            board.count_pieces(Color::W),
            0,
            "Empty board should have no white pieces"
        );

        // Add pieces and count
        let board = test_board! {
            N: B;
            E: W;
            S: B
        };

        assert_eq!(
            board.count_pieces(Color::B),
            2,
            "Should have 2 black pieces"
        );
        assert_eq!(board.count_pieces(Color::W), 1, "Should have 1 white piece");
    }

    #[test]
    fn test_get_pieces_at() {
        let board = Board::default();

        // Check if empty position returns empty array
        assert!(
            board.get_pieces_at(Position::N).is_empty(),
            "Empty position should have no pieces"
        );

        // Add a single piece
        let board = test_board! {
            N: B
        };
        assert_eq!(
            board.get_pieces_at(Position::N),
            vec![Color::B],
            "Position N should have one black piece"
        );

        // Add multiple pieces
        let board = test_board! {
            E: W, B
        };
        assert_eq!(
            board.get_pieces_at(Position::E),
            vec![Color::W, Color::B],
            "Position E should have pieces in order [white, black] from bottom"
        );
    }

    #[test]
    fn test_lines_up() {
        // Check win condition with 3 vertical black pieces
        let board = test_board! {
            N: B, B, B
        };
        assert!(
            board.lines_up(Color::B),
            "Three vertical black pieces should satisfy win condition"
        );
        assert!(
            !board.lines_up(Color::W),
            "White pieces should not satisfy win condition"
        );

        // Need to verify the definition of win condition
        // For 4 horizontal pieces, they need to be adjacent
        let board = test_board! {
            N: B;
            NE: B;
            E: B;
            SE: B
        };
        assert!(
            board.lines_up(Color::B),
            "Four adjacent black pieces should satisfy win condition"
        );

        // Pattern that doesn't satisfy win condition
        let board = test_board! {
            N: B;
            S: B
        };
        assert!(
            !board.lines_up(Color::B),
            "Non-consecutive pieces should not satisfy win condition"
        );
    }

    #[test]
    fn test_apply() {
        let mut board = Board::default();

        // Check if Put operation is correctly applied
        assert!(board.apply(Action::Put(Position::N, Color::B)).is_ok());
        assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);

        // Check if Move operation is correctly applied
        assert!(board.apply(Action::Move(Position::N, Position::E)).is_ok());
        assert!(board.get_pieces_at(Position::N).is_empty());
        assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);

        // Check if invalid operation is rejected
        let result = board.apply(Action::Move(Position::N, Position::S)); // N is empty
        assert!(result.is_err());
    }

    #[test]
    fn test_apply_unchecked() {
        let mut board = Board::default();

        // Check if Put operation is applied without validation
        board.apply_unchecked(Action::Put(Position::N, Color::B));
        assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);

        // Check if Move operation is applied without validation
        board.apply_unchecked(Action::Move(Position::N, Position::E));
        assert!(board.get_pieces_at(Position::N).is_empty());
        assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);
    }

    #[test]
    fn test_put() {
        let mut board = Board::default();

        // Check if a piece can be placed in an empty position
        assert!(board.put(Position::N, Color::B).is_ok());
        assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);

        // Check if a piece cannot be placed in a full position
        let mut board = test_board! {
            N: B, B, B
        };
        assert!(board.put(Position::N, Color::W).is_err());
    }

    #[test]
    fn test_put_unchecked() {
        let mut board = Board::default();

        // Check if a piece can be placed without validation
        board.put_unchecked(Position::N, Color::B);
        assert_eq!(board.get_pieces_at(Position::N), vec![Color::B]);
    }

    #[test]
    fn test_remove() {
        let mut board = test_board! {
            N: B
        };

        // Remove a piece and check if the color is correct
        let removed = board.remove(Position::N);
        assert!(removed.is_ok());
        assert_eq!(removed.unwrap(), Color::B);
        assert!(board.get_pieces_at(Position::N).is_empty());

        // Check if error occurs when removing from an empty position
        assert!(board.remove(Position::N).is_err());
    }

    #[test]
    fn test_remove_unchecked() {
        let mut board = test_board! {
            N: B
        };

        // Check if a piece can be removed without validation
        let removed = board.remove_unchecked(Position::N);
        assert_eq!(removed, Color::B);
        assert!(board.get_pieces_at(Position::N).is_empty());
    }

    #[test]
    fn test_move() {
        let mut board = test_board! {
            N: B
        };

        // Check if a legal move succeeds
        assert!(board.move_(Position::N, Position::E).is_ok());
        assert!(board.get_pieces_at(Position::N).is_empty());
        assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);

        // Check if an illegal move fails
        assert!(board.move_(Position::N, Position::S).is_err()); // N is empty
    }

    #[test]
    fn test_move_unchecked() {
        let mut board = test_board! {
            N: B
        };

        // Check if a piece can be moved without validation
        board.move_unchecked(Position::N, Position::E);
        assert!(board.get_pieces_at(Position::N).is_empty());
        assert_eq!(board.get_pieces_at(Position::E), vec![Color::B]);
    }

    #[test]
    fn test_from_inner() {
        // Test creating Board from default BitBoard
        let bit_board = BitBoard::default();
        let board = Board::from_inner(bit_board);
        assert!(board.is_valid(), "Board created from default BitBoard should be valid");
        assert_eq!(board.count_pieces(Color::B), 0, "Board should have no black pieces");
        assert_eq!(board.count_pieces(Color::W), 0, "Board should have no white pieces");

        // Test creating Board from custom BitBoard
        let custom_bit_board = BitBoard::new(0x123); // Some valid pattern
        let board = Board::from_inner(custom_bit_board);
        assert_eq!(board.inner(), &custom_bit_board, "Inner BitBoard should match");
    }
}
