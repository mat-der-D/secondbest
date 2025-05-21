//! Game state management module.
//!
//! This module provides the core game logic for the Second Best game, including:
//! - Game state representation and manipulation
//! - Turn management
//! - Action validation and application
//! - Win condition checking
//! - Second best declaration handling
//!
//! The main type in this module is `Game`, which encapsulates the complete game state
//! and provides methods to interact with it according to the game rules.
//!
//! Please refer to the examples in the `Game` documentation for usage examples.

use crate::board::{Action, Board, Color};
use crate::error::GameError;

/// Represents the state of a Second Best game.
///
/// This struct maintains the complete game state including the board,
/// player turns, action history, and legal moves.
///
/// # Examples
///
/// ```
/// use secondbest::prelude::*;
///
/// // Create a new game
/// let mut game = Game::new();
///
/// // Apply some actions
/// game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
/// game.apply_action(Action::Put(Position::S, Color::W)).unwrap();
///
/// // Check if second best can be declared
/// if game.can_declare_second_best() {
///     game.declare_second_best().unwrap();
/// }
///
/// // Check the game result
/// match game.result() {
///     GameResult::Finished { winner } => println!("Winner: {:?}", winner),
///     GameResult::InProgress => println!("Game still in progress"),
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Game {
    board: Board,
    prev_state: Option<(Board, Action)>,
    current_player: Color,
    forbidden_action: Option<Action>,
    legal_actions: Vec<Action>,
}

impl std::default::Default for Game {
    fn default() -> Self {
        Self::new()
    }
}

impl Game {
    /// Creates a new game with the default initial state.
    ///
    /// The game starts with an empty board and Black as the first player.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let game = Game::new();
    /// assert!(matches!(game.result(), GameResult::InProgress));
    /// ```
    pub fn new() -> Self {
        let board = Board::default();
        let first_player = Color::B;
        Self {
            board,
            prev_state: None,
            current_player: first_player,
            forbidden_action: None,
            legal_actions: Self::collect_legal_actions(board, first_player, None),
        }
    }

    /// Returns a reference to the current game board.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let game = Game::new();
    /// let board = game.board();
    /// assert_eq!(board.count_pieces(Color::B), 0);
    /// assert_eq!(board.count_pieces(Color::W), 0);
    /// ```
    pub fn board(&self) -> &Board {
        &self.board
    }

    /// Returns the current player.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let game = Game::new();
    /// assert_eq!(game.current_player(), Color::B);
    /// ```
    pub fn current_player(&self) -> Color {
        self.current_player
    }

    /// Checks if a given action is legal in the current game state.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let game = Game::new();
    /// // In a new game, placing a black piece at any position is legal
    /// assert!(game.is_legal_action(Action::Put(Position::N, Color::B)));
    /// // But placing a white piece is not (it's not white's turn)
    /// assert!(!game.is_legal_action(Action::Put(Position::N, Color::W)));
    /// ```
    pub fn is_legal_action(&self, action: Action) -> bool {
        self.legal_actions.contains(&action)
    }

    /// Returns a slice of all legal actions for the current player.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let game = Game::new();
    /// let legal_actions = game.legal_actions();
    /// // In a new game, there are 8 legal actions (placing a black piece at any position)
    /// assert_eq!(legal_actions.len(), 8);
    /// ```
    pub fn legal_actions(&self) -> &[Action] {
        &self.legal_actions
    }

    /// Applies an action to the game state.
    ///
    /// This method updates the board, switches the current player,
    /// and recalculates legal actions for the next player.
    ///
    /// # Errors
    ///
    /// Returns `GameError::GameAlreadyOver` if the game has already finished.
    /// Returns `GameError::IllegalAction` if the action is not legal in the current state.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let mut game = Game::new();
    /// // Apply a legal action
    /// assert!(game.apply_action(Action::Put(Position::N, Color::B)).is_ok());
    ///
    /// // Trying to apply an illegal action (not white's turn)
    /// let current_player = game.current_player();
    /// assert_eq!(current_player, Color::W);
    /// assert!(game.apply_action(Action::Put(Position::S, Color::B)).is_err());
    /// ```
    pub fn apply_action(&mut self, action: Action) -> Result<(), GameError> {
        if matches!(self.result(), GameResult::Finished { .. }) {
            return Err(GameError::GameAlreadyOver);
        }

        if !self.is_legal_action(action) {
            return Err(GameError::IllegalAction(action));
        }

        let prev_board = self.board;
        self.board.apply_unchecked(action);
        self.prev_state = match self.forbidden_action {
            None => Some((prev_board, action)), // 1st time
            Some(_) => None,                    // 2nd time
        };
        let next_player = self.current_player.opposite();
        self.current_player = next_player;
        self.forbidden_action = None;
        self.legal_actions = Self::collect_legal_actions(self.board, next_player, None);
        Ok(())
    }

    /// Checks if the current player can declare "second best".
    ///
    /// A player can declare "second best" only after their opponent's first move
    /// in a turn (not after a second move following a previous "second best" declaration).
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let mut game = Game::new();
    /// // Initially, second best cannot be declared
    /// assert!(!game.can_declare_second_best());
    ///
    /// // After an action, the next player can declare second best
    /// game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
    /// assert!(game.can_declare_second_best());
    /// assert_eq!(game.current_player(), Color::W);
    /// ```
    pub fn can_declare_second_best(&self) -> bool {
        self.prev_state.is_some()
    }

    /// Declares "second best", forcing the opponent to choose a different action.
    ///
    /// This method reverts the board to its previous state, switches back to the previous player,
    /// and marks the previous action as forbidden.
    ///
    /// # Errors
    ///
    /// Returns `GameError::CannotDeclareSecondBest` if "second best" cannot be declared
    /// in the current state.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let mut game = Game::new();
    /// // Apply an action
    /// game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
    /// assert_eq!(game.current_player(), Color::W);
    ///
    /// // Declare second best
    /// assert!(game.declare_second_best().is_ok());
    ///
    /// // The turn goes back to the previous player
    /// assert_eq!(game.current_player(), Color::B);
    /// // The previous action is now forbidden
    /// assert!(!game.is_legal_action(Action::Put(Position::N, Color::B)));
    /// ```
    pub fn declare_second_best(&mut self) -> Result<(), GameError> {
        let Some((prev_board, prev_action)) = self.prev_state.take() else {
            return Err(GameError::CannotDeclareSecondBest);
        };

        self.board = prev_board;
        let prev_player = self.current_player.opposite();
        self.current_player = prev_player;
        self.forbidden_action = Some(prev_action);
        self.legal_actions =
            Self::collect_legal_actions(self.board, prev_player, Some(prev_action));
        Ok(())
    }

    /// Collects all legal actions for a player in a given board state.
    ///
    /// # Arguments
    /// * `board` - The board state to analyze
    /// * `player` - The player whose legal actions to collect
    /// * `forbidden_action` - An optional action that is forbidden (after "second best" declaration)
    ///
    /// # Returns
    /// * A vector of all legal actions for the specified player
    fn collect_legal_actions(
        board: Board,
        player: Color,
        forbidden_action: Option<Action>,
    ) -> Vec<Action> {
        if board.lines_up(player) || board.lines_up(player.opposite()) {
            return Vec::new();
        }

        let num_pieces = board.count_pieces(player);

        board
            .legal_action_iter(player)
            .filter(|&a| {
                if num_pieces < 8 {
                    matches!(a, Action::Put(..))
                } else {
                    matches!(a, Action::Move(..))
                }
            })
            .filter(|&a| Some(a) != forbidden_action)
            .collect()
    }

    /// Determines the current result of the game.
    ///
    /// The game is considered finished when:
    /// - A player has achieved a winning condition (3 pieces in a stack or 4 consecutive top pieces)
    /// - If both players achieve a winning condition simultaneously, the player who made the last move wins
    /// - If a player has no legal moves available, they lose
    ///
    /// Note: Winning conditions are only checked after all "second best" declarations have been used.
    ///
    /// # Examples
    ///
    /// ```
    /// use secondbest::prelude::*;
    ///
    /// let mut game = Game::new();
    /// // Initially, the game is in progress
    /// assert!(matches!(game.result(), GameResult::InProgress));
    ///
    /// // Create a sequence of moves
    /// game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
    /// game.apply_action(Action::Put(Position::S, Color::W)).unwrap();
    /// // Game is still in progress at this intermediate stage
    /// assert!(matches!(game.result(), GameResult::InProgress));
    ///
    /// game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
    /// game.apply_action(Action::Put(Position::S, Color::W)).unwrap();
    /// game.apply_action(Action::Put(Position::E, Color::B)).unwrap();
    ///
    /// // White declares "second best"
    /// assert_eq!(game.current_player(), Color::W);
    /// game.declare_second_best().unwrap();
    ///
    /// // Black makes a winning move by stacking 3 pieces at North
    /// assert_eq!(game.current_player(), Color::B);
    /// game.apply_action(Action::Put(Position::N, Color::B)).unwrap();
    ///
    /// // Game is finished with Black as the winner
    /// assert_eq!(game.result().winner(), Some(Color::B));
    /// ```
    pub fn result(&self) -> GameResult {
        if self.can_declare_second_best() {
            return GameResult::InProgress;
        }

        let prev_player = self.current_player.opposite();
        if self.board.lines_up(prev_player) {
            GameResult::with_winner(prev_player)
        } else if self.board.lines_up(self.current_player) {
            GameResult::with_winner(self.current_player)
        } else if self.legal_actions.is_empty() {
            GameResult::with_winner(prev_player)
        } else {
            GameResult::InProgress
        }
    }
}

impl std::fmt::Display for Game {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Board state:")?;
        writeln!(f, "{}", self.board)?;
        writeln!(f, "Current player: {:?}", self.current_player)?;
        writeln!(f, "{}", self.result())?;

        Ok(())
    }
}

/// Represents the result of a game.
///
/// This enum has two variants:
/// - `Finished`: Indicates the game has ended with a winner
/// - `InProgress`: Indicates the game is still ongoing
///
/// # Examples
///
/// ```
/// use secondbest::prelude::*;
///
/// let mut game = Game::new();
/// assert!(matches!(game.result(), GameResult::InProgress));
///
/// // After a winning move
/// // ...
/// // Check if there's a winner
/// if let Some(winner) = game.result().winner() {
///     println!("The winner is: {:?}", winner);
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GameResult {
    /// Indicates the game has finished with a winner
    Finished { winner: Color },
    /// Indicates the game is still in progress
    InProgress,
}

impl GameResult {
    /// Creates a new `GameResult::Finished` with the specified winner.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use secondbest::prelude::*;
    ///
    /// let result = GameResult::with_winner(Color::B);
    /// assert_eq!(result.winner(), Some(Color::B));
    /// ```
    fn with_winner(winner: Color) -> Self {
        GameResult::Finished { winner }
    }

    /// Returns the winner of the game, if any.
    ///
    /// Returns `Some(Color)` if the game is finished, or `None` if the game is still in progress.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use secondbest::prelude::*;
    ///
    /// let in_progress = GameResult::InProgress;
    /// assert_eq!(in_progress.winner(), None);
    ///
    /// let finished = GameResult::with_winner(Color::W);
    /// assert_eq!(finished.winner(), Some(Color::W));
    /// ```
    pub fn winner(&self) -> Option<Color> {
        use GameResult::*;
        match self {
            Finished { winner } => Some(*winner),
            InProgress => None,
        }
    }
}

impl std::fmt::Display for GameResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GameResult::Finished { winner } => write!(f, "Game over - Winner: {}", winner),
            GameResult::InProgress => write!(f, "Game in progress"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[derive(Debug, Clone)]
    struct RandomGameGenerator {
        game: Game,
        num: usize,
    }

    impl RandomGameGenerator {
        pub fn new(num: usize) -> Self {
            Self {
                game: Game::new(),
                num,
            }
        }

        pub fn num(&self) -> usize {
            self.num
        }
    }

    impl Iterator for RandomGameGenerator {
        type Item = (Game, Option<Action>);
        fn next(&mut self) -> Option<Self::Item> {
            fn next_rand(state: usize) -> usize {
                state.wrapping_mul(6364136223846793005).wrapping_add(1)
            }

            if self.game.result().winner().is_some() {
                return None;
            }

            if self.game.can_declare_second_best() {
                self.game.declare_second_best().unwrap();
                return Some((self.game.clone(), None));
            }

            let legal_actions = self.game.legal_actions();
            if legal_actions.is_empty() {
                return None;
            }
            let action = legal_actions[self.num % legal_actions.len()];
            self.num = next_rand(self.num);
            self.game.apply_action(action).unwrap();
            Some((self.game.clone(), Some(action)))
        }
    }

    #[test]
    fn test_new() {
        let game = Game::new();
        assert_eq!(*game.board(), Board::default());
        assert_eq!(game.current_player(), Color::B);
    }

    #[test]
    fn test_board() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            let mut board = Board::default();
            for (game, action) in &mut generator {
                if let Some(a) = action {
                    assert!(board.apply(a).is_ok());
                    assert_eq!(*game.board(), board);
                } else {
                    board = *game.board();
                }
            }
            seed = generator.num();
        }
    }

    #[test]
    fn test_current_player() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, _) in &mut generator {
                if game.result().winner().is_some() {
                    continue;
                }

                let player = game.current_player();
                for &action in game.legal_actions() {
                    let mut game = game.clone();
                    assert!(game.apply_action(action).is_ok());
                    let next_player = game.current_player();
                    assert_eq!(next_player, player.opposite());
                }
            }
            seed = generator.num();
        }
    }

    #[test]
    fn test_is_legal_action() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, _) in &mut generator {
                test_is_legal_action_impl(&game);
            }
            seed = generator.num();
        }
    }

    fn test_is_legal_action_impl(game: &Game) {
        if game.result().winner().is_some() {
            return;
        }

        let lines_up = game.board().lines_up(Color::B) || game.board().lines_up(Color::W);
        let player = game.current_player();
        let num_pieces = game.board().count_pieces(player);

        // test put
        for pos in Position::iter() {
            for color in [Color::B, Color::W] {
                let action = Action::Put(pos, color);
                if color != player {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                if num_pieces >= 8 {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                if lines_up {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                if game.forbidden_action == Some(action) {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                assert_eq!(
                    game.board().get_pieces_at(pos).len() < 3,
                    game.is_legal_action(action)
                );
            }
        }

        // test move
        for from in Position::iter() {
            use Position::*;
            let legal_dsts = match from {
                N => [NE, NW, S],
                NE => [N, E, SW],
                E => [NE, SE, W],
                SE => [E, S, NW],
                S => [SE, SW, N],
                SW => [S, W, NE],
                W => [SW, NW, E],
                NW => [W, N, SE],
            };

            for to in Position::iter() {
                let action = Action::Move(from, to);
                if num_pieces < 8 {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                if lines_up {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                if !legal_dsts.contains(&to) {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                if game.forbidden_action == Some(action) {
                    assert!(!game.is_legal_action(action));
                    continue;
                }
                let pieces_src = game.board().get_pieces_at(from);
                let pieces_dst = game.board().get_pieces_at(to);
                assert_eq!(
                    (pieces_src.last() == Some(&player)) && (pieces_dst.len() < 3),
                    game.is_legal_action(action)
                );
            }
        }
    }

    #[test]
    fn test_legal_actions() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, _) in &mut generator {
                test_legal_actions_impl(&game);
            }
            seed = generator.num();
        }
    }

    fn test_legal_actions_impl(game: &Game) {
        // test put
        for pos in Position::iter() {
            for color in [Color::B, Color::W] {
                let action = Action::Put(pos, color);
                assert_eq!(
                    game.legal_actions().contains(&action),
                    game.is_legal_action(action)
                );
            }
        }

        // test move
        for from in Position::iter() {
            for to in Position::iter() {
                let action = Action::Move(from, to);
                assert_eq!(
                    game.legal_actions().contains(&action),
                    game.is_legal_action(action)
                );
            }
        }
    }

    #[test]
    fn test_apply_action() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, _) in &mut generator {
                // test put
                for pos in Position::iter() {
                    for color in [Color::B, Color::W] {
                        let action = Action::Put(pos, color);
                        let mut game = game.clone();
                        assert_eq!(
                            game.is_legal_action(action),
                            game.apply_action(action).is_ok()
                        );
                    }
                }

                // test move
                for from in Position::iter() {
                    for to in Position::iter() {
                        let action = Action::Move(from, to);
                        let mut game = game.clone();
                        assert_eq!(
                            game.is_legal_action(action),
                            game.apply_action(action).is_ok()
                        );
                    }
                }
            }
            seed = generator.num();
        }
    }

    #[test]
    fn test_can_declare_second_best() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, prev_action) in &mut generator {
                for &action in game.legal_actions() {
                    let mut game = game.clone();
                    assert!(game.apply_action(action).is_ok());
                    assert_eq!(game.can_declare_second_best(), prev_action.is_some());
                }
            }
            seed = generator.num();
        }
    }

    #[test]
    fn test_declare_second_best() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, _) in &mut generator {
                let prev_board = game.board();
                for &action in game.legal_actions() {
                    let mut game = game.clone();
                    assert!(game.apply_action(action).is_ok());
                    let can_declare = game.can_declare_second_best();
                    assert_eq!(game.declare_second_best().is_ok(), can_declare);
                    if can_declare {
                        assert_eq!(game.board(), prev_board);
                    }
                }
            }
            seed = generator.num();
        }
    }

    #[test]
    fn test_result() {
        const NUM_GAMES: usize = 5;
        let mut seed = 12345;
        for _ in 0..NUM_GAMES {
            let mut generator = RandomGameGenerator::new(seed);
            for (game, _) in &mut generator {
                let result = game.result();
                if game.can_declare_second_best() {
                    assert!(matches!(result, GameResult::InProgress));
                    continue;
                }
                let player = game.current_player();
                let opponent = player.opposite();
                let board = game.board();
                match (board.lines_up(player), board.lines_up(player.opposite())) {
                    (true, false) => assert_eq!(result, GameResult::Finished { winner: player }),
                    (false, true) => assert_eq!(result, GameResult::Finished { winner: opponent }),
                    (true, true) => assert_eq!(result, GameResult::Finished { winner: opponent }),
                    (false, false) => {
                        if game.legal_actions().is_empty() {
                            assert_eq!(result, GameResult::Finished { winner: opponent })
                        } else {
                            assert_eq!(result, GameResult::InProgress)
                        }
                    }
                }
            }
            seed = generator.num();
        }
    }
}
