//! Iterators for legal game actions.
//!
//! This module provides iterators for traversing legal actions in the game:
//! - `BitLegalPutIter`: Low-level iterator for legal piece placements
//! - `BitLegalMoveIter`: Low-level iterator for legal piece movements
//! - `LegalActionIter`: Combined iterator for all legal actions
//!
//! These iterators allow efficient enumeration of possible moves for a player
//! during their turn, supporting both the bit-based board representation and
//! the higher-level game abstractions.

use crate::board::bitboard::BitBoard;
use crate::board::types::{Action, Position};

/// Iterator for all legal actions (both puts and moves) in the current board state.
#[derive(Debug)]
pub struct LegalActionIter {
    iter: std::iter::Chain<LegalPutIter, LegalMoveIter>,
}

impl LegalActionIter {
    pub(crate) fn new(put_iter: LegalPutIter, move_iter: LegalMoveIter) -> Self {
        Self {
            iter: put_iter.chain(move_iter),
        }
    }
}

impl Iterator for LegalActionIter {
    type Item = Action;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// Iterator for legal put actions (placing a new piece on the board).
#[derive(Debug)]
pub(crate) struct LegalPutIter {
    bit_iter: BitLegalPutIter,
}

impl LegalPutIter {
    pub(crate) fn new(bit_iter: BitLegalPutIter) -> Self {
        LegalPutIter { bit_iter }
    }
}

impl Iterator for LegalPutIter {
    type Item = Action;
    fn next(&mut self) -> Option<Self::Item> {
        let (pos, color) = self.bit_iter.next()?;
        let pos = unsafe { Position::from_u32_unchecked(pos) };
        Some(Action::Put(pos, color.into()))
    }
}

/// Iterator for legal move actions (moving a piece from one position to another).
#[derive(Debug)]
pub(crate) struct LegalMoveIter {
    bit_iter: BitLegalMoveIter,
}

impl LegalMoveIter {
    pub(crate) fn new(bit_iter: BitLegalMoveIter) -> Self {
        LegalMoveIter { bit_iter }
    }
}

impl Iterator for LegalMoveIter {
    type Item = Action;
    fn next(&mut self) -> Option<Self::Item> {
        let (from, to) = self.bit_iter.next()?;
        let from = unsafe { Position::from_u32_unchecked(from) };
        let to = unsafe { Position::from_u32_unchecked(to) };
        Some(Action::Move(from, to))
    }
}

/// Low-level iterator for legal put actions using bit representation.
#[derive(Debug)]
pub struct BitLegalPutIter {
    pos_iter: HotBitIter,
    color: bool,
}

impl BitLegalPutIter {
    pub(crate) fn new(board: BitBoard, color: bool) -> Self {
        let pos_iter = HotBitIter::new((board.bits() << 3) & 0x8888_8888); // 0x8 = 0b1000
        Self { pos_iter, color }
    }
}

impl Iterator for BitLegalPutIter {
    type Item = (u32, bool);
    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.pos_iter.next()?;
        Some((pos, self.color))
    }
}

/// Low-level iterator for legal move actions using bit representation.
#[derive(Debug)]
pub struct BitLegalMoveIter {
    from_iter: HotBitIter,
    to_filter: u32,
    from: u32,
    to_iter: HotBitIter,
}

impl BitLegalMoveIter {
    pub(crate) fn new(board: BitBoard, color: bool) -> Self {
        let bits = if color {
            board.bits()
        } else {
            !board.bits() - 0x1111_1111
        };

        Self {
            from_iter: HotBitIter::new(bits & 0x8888_8888), // 0x8 = 0b1000
            to_filter: (bits << 3) & 0x8888_8888,           // 0x8 = 0b1000,
            from: 0,                                        // dummy
            to_iter: HotBitIter::new(0),                    // empty
        }
    }
}

impl Iterator for BitLegalMoveIter {
    type Item = (u32, u32);
    fn next(&mut self) -> Option<Self::Item> {
        const TO_BITS_BASE: u32 = 0x1001_0010; // adjacent and opposite side

        loop {
            if let Some(to) = self.to_iter.next() {
                return Some((self.from, to));
            }
            let from = self.from_iter.next()?;
            let to_bits = TO_BITS_BASE.rotate_left(from.trailing_zeros()) & self.to_filter;
            (self.from, self.to_iter) = (from, HotBitIter::new(to_bits))
        }
    }
}

/// Iterator for set bits in a 32-bit integer, optimized for board operations.
#[derive(Debug)]
pub(crate) struct HotBitIter {
    bits: u32,
}

impl HotBitIter {
    pub(crate) fn new(bits: u32) -> Self {
        Self { bits }
    }
}

impl Iterator for HotBitIter {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits == 0 {
            return None;
        }

        let bit = self.bits & (!self.bits + 1);
        self.bits ^= bit;
        Some(bit)
    }
}

impl std::iter::FusedIterator for HotBitIter {}
impl std::iter::FusedIterator for BitLegalPutIter {}
impl std::iter::FusedIterator for BitLegalMoveIter {}
impl std::iter::FusedIterator for LegalPutIter {}
impl std::iter::FusedIterator for LegalMoveIter {}
impl std::iter::FusedIterator for LegalActionIter {}
