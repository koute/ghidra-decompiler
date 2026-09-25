use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::address::{
    SeqNum, bit_transitions, calc_mask, count_leading_zeros, leastsigbit_set, mostsigbit_set, sign_extend,
    sign_extend_size,
};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::{OpCode, get_opname};
use crate::varnode::VarnodeId;

#[derive(Clone, Debug)]
pub struct CircleRange {
    left: u64,
    right: u64,
    mask: u64,
    isempty: bool,
    step: i32,
}

fn step_value(step: i32) -> u64 {
    step as i64 as u64
}

impl CircleRange {
    pub const ARRANGE: &'static [u8] = b"gcgbegdagggggggeggggcgbggggggggcdfgggggggegdggggbgggfggggcgbegda";

    pub fn new() -> CircleRange {
        CircleRange {
            left: 0,
            right: 0,
            mask: 0,
            isempty: true,
            step: 0,
        }
    }

    pub fn new_range(lft: u64, rgt: u64, size: i32, stp: i32) -> CircleRange {
        let mask = calc_mask(size);
        CircleRange {
            left: lft & mask,
            right: rgt & mask,
            mask,
            isempty: false,
            step: stp,
        }
    }

    pub fn new_bool(val: bool) -> CircleRange {
        CircleRange {
            left: if val { 1 } else { 0 },
            right: val as u64 + 1,
            mask: 0xff,
            isempty: false,
            step: 1,
        }
    }

    pub fn new_single(val: u64, size: i32) -> CircleRange {
        let mask = calc_mask(size);
        CircleRange {
            left: val,
            right: val.wrapping_add(1) & mask,
            mask,
            isempty: false,
            step: 1,
        }
    }

    fn normalize(&mut self) {
        if self.left == self.right {
            if self.step != 1 {
                self.left %= step_value(self.step);
            } else {
                self.left = 0;
            }
            self.right = self.left;
        }
    }

    fn complement(&mut self) {
        if self.isempty {
            self.left = 0;
            self.right = 0;
            self.isempty = false;
            return;
        }
        if self.left == self.right {
            self.isempty = true;
            return;
        }
        std::mem::swap(&mut self.left, &mut self.right);
    }

    fn convert_to_boolean(&mut self) -> bool {
        if self.isempty {
            return false;
        }
        let contains_zero = self.contains(0);
        let contains_one = self.contains(1);
        self.mask = 0xff;
        self.step = 1;
        if contains_zero && contains_one {
            self.left = 0;
            self.right = 2;
            self.isempty = false;
            return true;
        } else if contains_zero {
            self.left = 0;
            self.right = 1;
            self.isempty = false;
        } else if contains_one {
            self.left = 1;
            self.right = 2;
            self.isempty = false;
        } else {
            self.isempty = true;
        }
        false
    }

    fn new_stride(mask: u64, step: i32, old_step: i32, rem: u32, myleft: &mut u64, myright: &mut u64) -> bool {
        if old_step != 1 {
            let old_rem = (*myleft % step_value(old_step)) as u32;
            if old_rem != rem % (old_step as u32) {
                return true;
            }
        }
        let orig_order = *myleft < *myright;
        let left_rem = (*myleft % step_value(step)) as u32;
        let right_rem = (*myright % step_value(step)) as u32;
        if left_rem > rem {
            *myleft = myleft.wrapping_add(rem.wrapping_add(step as u32).wrapping_sub(left_rem) as u64);
        } else {
            *myleft = myleft.wrapping_add(rem.wrapping_sub(left_rem) as u64);
        }
        if right_rem > rem {
            *myright = myright.wrapping_add(rem.wrapping_add(step as u32).wrapping_sub(right_rem) as u64);
        } else {
            *myright = myright.wrapping_add(rem.wrapping_sub(right_rem) as u64);
        }
        *myleft &= mask;
        *myright &= mask;
        let new_order = *myleft < *myright;
        if orig_order != new_order {
            return true;
        }
        false
    }

    fn new_domain(new_mask: u64, new_step: i32, myleft: &mut u64, myright: &mut u64) -> bool {
        let rem = if new_step != 1 {
            *myleft % step_value(new_step)
        } else {
            0
        };
        if *myleft > new_mask {
            if *myright > new_mask {
                if *myleft < *myright {
                    return true;
                }
                *myleft = rem;
                *myright = rem;
                return false;
            }
            *myleft = rem;
        }
        if *myright > new_mask {
            *myright = rem;
        }
        if *myleft == *myright {
            *myleft = rem;
            *myright = rem;
        }
        false
    }

    fn encode_range_overlaps(op1left: u64, op1right: u64, op2left: u64, op2right: u64) -> u8 {
        let mut val: usize = if op1left <= op1right { 0x20 } else { 0 };
        val |= if op1left <= op2left { 0x10 } else { 0 };
        val |= if op1left <= op2right { 0x8 } else { 0 };
        val |= if op1right <= op2left { 4 } else { 0 };
        val |= if op1right <= op2right { 2 } else { 0 };
        val |= if op2left <= op2right { 1 } else { 0 };
        CircleRange::ARRANGE[val]
    }

    pub fn set_range(&mut self, lft: u64, rgt: u64, size: i32, step: i32) {
        self.mask = calc_mask(size);
        self.left = lft & self.mask;
        self.right = rgt & self.mask;
        self.step = step;
        self.isempty = false;
    }

    pub fn set_range_single(&mut self, val: u64, size: i32) {
        self.mask = calc_mask(size);
        self.step = 1;
        self.left = val;
        self.right = self.left.wrapping_add(1) & self.mask;
        self.isempty = false;
    }

    pub fn set_full(&mut self, size: i32) {
        self.mask = calc_mask(size);
        self.step = 1;
        self.left = 0;
        self.right = 0;
        self.isempty = false;
    }

    pub fn is_empty(&self) -> bool {
        self.isempty
    }

    pub fn is_full(&self) -> bool {
        (!self.isempty) && (self.step == 1) && (self.left == self.right)
    }

    pub fn is_single(&self) -> bool {
        (!self.isempty) && (self.right == (self.left.wrapping_add(step_value(self.step)) & self.mask))
    }

    pub fn get_min(&self) -> u64 {
        self.left
    }

    pub fn get_max(&self) -> u64 {
        self.right.wrapping_sub(step_value(self.step)) & self.mask
    }

    pub fn get_end(&self) -> u64 {
        self.right
    }

    pub fn get_mask(&self) -> u64 {
        self.mask
    }

    pub fn get_size(&self) -> u64 {
        if self.isempty {
            return 0;
        }
        let step = step_value(self.step);
        let mut val;
        if self.left < self.right {
            val = (self.right - self.left) / step;
        } else {
            val = self
                .mask
                .wrapping_sub(self.left.wrapping_sub(self.right))
                .wrapping_add(step)
                / step;
            if val == 0 {
                val = self.mask;
                if self.step > 1 {
                    val /= step;
                    val += 1;
                }
            }
        }
        val
    }

    pub fn get_step(&self) -> i32 {
        self.step
    }

    pub fn get_max_info(&self) -> i32 {
        let half_point = self.mask ^ (self.mask >> 1);
        if self.contains(half_point) {
            return 64 - count_leading_zeros(half_point);
        }
        let size_left = if (half_point & self.left) == 0 {
            count_leading_zeros(self.left)
        } else {
            count_leading_zeros(!self.left & self.mask)
        };
        let size_right = if (half_point & self.right) == 0 {
            count_leading_zeros(self.right)
        } else {
            count_leading_zeros(!self.right & self.mask)
        };
        64 - if size_right < size_left { size_right } else { size_left }
    }

    pub fn get_next(&self, val: &mut u64) -> bool {
        *val = val.wrapping_add(step_value(self.step)) & self.mask;
        *val != self.right
    }

    pub fn contains_range(&self, op2: &CircleRange) -> bool {
        if self.isempty {
            return op2.isempty;
        }
        if op2.isempty {
            return true;
        }
        if self.step > op2.step && !op2.is_single() {
            return false;
        }
        if self.left == self.right {
            return true;
        }
        if op2.left == op2.right {
            return false;
        }
        if self.left % step_value(self.step) != op2.left % step_value(self.step) {
            return false;
        }
        if self.left == op2.left && self.right == op2.right {
            return true;
        }
        let overlap_code = CircleRange::encode_range_overlaps(self.left, self.right, op2.left, op2.right);
        if overlap_code == b'c' {
            return true;
        }
        if overlap_code == b'b' && (self.right == op2.right) {
            return true;
        }
        false
    }

    pub fn contains(&self, val: u64) -> bool {
        if self.isempty {
            return false;
        }
        if self.step != 1 && (self.left % step_value(self.step)) != (val % step_value(self.step)) {
            return false;
        }
        if self.left < self.right {
            if val < self.left {
                return false;
            }
            if self.right <= val {
                return false;
            }
        } else if self.right < self.left {
            if val < self.right {
                return true;
            }
            if val >= self.left {
                return true;
            }
            return false;
        }
        true
    }

    pub fn intersect(&mut self, op2: &CircleRange) -> i32 {
        if self.isempty {
            return 0;
        }
        if op2.isempty {
            self.isempty = true;
            return 0;
        }
        let mut myleft = self.left;
        let mut myright = self.right;
        let mut op2left = op2.left;
        let mut op2right = op2.right;
        let new_step;
        if self.step < op2.step {
            new_step = op2.step;
            let rem = (op2left % step_value(new_step)) as u32;
            if CircleRange::new_stride(self.mask, new_step, self.step, rem, &mut myleft, &mut myright) {
                self.isempty = true;
                return 0;
            }
        } else if op2.step < self.step {
            new_step = self.step;
            let rem = (myleft % step_value(new_step)) as u32;
            if CircleRange::new_stride(op2.mask, new_step, op2.step, rem, &mut op2left, &mut op2right) {
                self.isempty = true;
                return 0;
            }
        } else {
            new_step = self.step;
        }
        let new_mask = self.mask & op2.mask;
        if self.mask != new_mask {
            if CircleRange::new_domain(new_mask, new_step, &mut myleft, &mut myright) {
                self.isempty = true;
                return 0;
            }
        } else if op2.mask != new_mask && CircleRange::new_domain(new_mask, new_step, &mut op2left, &mut op2right) {
            self.isempty = true;
            return 0;
        }
        let retval;
        if myleft == myright {
            self.left = op2left;
            self.right = op2right;
            retval = 0;
        } else if op2left == op2right {
            self.left = myleft;
            self.right = myright;
            retval = 0;
        } else {
            let overlap_code = CircleRange::encode_range_overlaps(myleft, myright, op2left, op2right);
            match overlap_code {
                b'a' | b'f' => {
                    self.isempty = true;
                    retval = 0;
                }
                b'b' => {
                    self.left = op2left;
                    self.right = myright;
                    if self.left == self.right {
                        self.isempty = true;
                    }
                    retval = 0;
                }
                b'c' => {
                    self.left = op2left;
                    self.right = op2right;
                    retval = 0;
                }
                b'd' => {
                    self.left = myleft;
                    self.right = myright;
                    retval = 0;
                }
                b'e' => {
                    self.left = myleft;
                    self.right = op2right;
                    if self.left == self.right {
                        self.isempty = true;
                    }
                    retval = 0;
                }
                b'g' => {
                    if myleft == op2right {
                        self.left = op2left;
                        self.right = myright;
                        if self.left == self.right {
                            self.isempty = true;
                        }
                        retval = 0;
                    } else if op2left == myright {
                        self.left = myleft;
                        self.right = op2right;
                        if self.left == self.right {
                            self.isempty = true;
                        }
                        retval = 0;
                    } else {
                        retval = 2;
                    }
                }
                _ => {
                    retval = 2;
                }
            }
        }
        if retval != 0 {
            return retval;
        }
        self.mask = new_mask;
        self.step = new_step;
        0
    }

    pub fn set_nz_mask(&mut self, nzmask: u64, size: i32) -> bool {
        let trans = bit_transitions(nzmask, size);
        if trans > 2 {
            return false;
        }
        let hasstep = (nzmask & 1) == 0;
        if (!hasstep) && (trans == 2) {
            return false;
        }
        self.isempty = false;
        if trans == 0 {
            self.mask = calc_mask(size);
            if hasstep {
                self.step = 1;
                self.left = 0;
                self.right = 1;
            } else {
                self.step = 1;
                self.left = 0;
                self.right = 0;
            }
            return true;
        }
        let shift = leastsigbit_set(nzmask);
        self.step = 1i32.wrapping_shl(shift as u32);
        self.mask = calc_mask(size);
        self.left = 0;
        self.right = nzmask.wrapping_add(step_value(self.step)) & self.mask;
        true
    }

    pub fn circle_union(&mut self, op2: &CircleRange) -> i32 {
        if op2.isempty {
            return 0;
        }
        if self.isempty {
            *self = op2.clone();
            return 0;
        }
        if self.mask != op2.mask {
            return 2;
        }
        let mut a_right = self.right;
        let mut b_right = op2.right;
        let mut new_step = self.step;
        if self.step < op2.step {
            if self.is_single() {
                new_step = op2.step;
                a_right = self.left.wrapping_add(step_value(new_step)) & self.mask;
            } else {
                return 2;
            }
        } else if op2.step < self.step {
            if op2.is_single() {
                new_step = self.step;
                b_right = op2.left.wrapping_add(step_value(new_step)) & self.mask;
            } else {
                return 2;
            }
        }
        let rem;
        if new_step != 1 {
            rem = self.left % step_value(new_step);
            if rem != (op2.left % step_value(new_step)) {
                return 2;
            }
        } else {
            rem = 0;
        }
        if (self.left == a_right) || (op2.left == b_right) {
            self.left = rem;
            self.right = rem;
            self.step = new_step;
            return 0;
        }
        let overlap_code = CircleRange::encode_range_overlaps(self.left, a_right, op2.left, b_right);
        match overlap_code {
            b'a' | b'f' => {
                if a_right == op2.left {
                    self.right = b_right;
                    self.step = new_step;
                    return 0;
                }
                if self.left == b_right {
                    self.left = op2.left;
                    self.right = a_right;
                    self.step = new_step;
                    return 0;
                }
                2
            }
            b'b' => {
                self.right = b_right;
                self.step = new_step;
                0
            }
            b'c' => {
                self.right = a_right;
                self.step = new_step;
                0
            }
            b'd' => {
                self.left = op2.left;
                self.right = b_right;
                self.step = new_step;
                0
            }
            b'e' => {
                self.left = op2.left;
                self.right = a_right;
                self.step = new_step;
                0
            }
            b'g' => {
                self.left = rem;
                self.right = rem;
                self.step = new_step;
                0
            }
            _ => -1,
        }
    }

    pub fn minimal_container(&mut self, op2: &CircleRange, max_step: i32) -> bool {
        if self.is_single() && op2.is_single() {
            let (min, max) = if self.get_min() < op2.get_min() {
                (self.get_min(), op2.get_min())
            } else {
                (op2.get_min(), self.get_min())
            };
            let diff = max.wrapping_sub(min);
            if diff > 0 && diff <= step_value(max_step) && leastsigbit_set(diff) == mostsigbit_set(diff) {
                self.step = diff as i32;
                self.left = min;
                self.right = max.wrapping_add(step_value(self.step)) & self.mask;
                return false;
            }
        }
        let a_right = self.right.wrapping_sub(step_value(self.step)).wrapping_add(1);
        let b_right = op2.right.wrapping_sub(step_value(op2.step)).wrapping_add(1);
        self.step = 1;
        self.mask |= op2.mask;
        let overlap_code = CircleRange::encode_range_overlaps(self.left, a_right, op2.left, b_right);
        match overlap_code {
            b'a' => {
                let vacant_size1 = self.left.wrapping_add(self.mask.wrapping_sub(b_right)).wrapping_add(1);
                let vacant_size2 = op2.left.wrapping_sub(a_right);
                if vacant_size1 < vacant_size2 {
                    self.left = op2.left;
                    self.right = a_right;
                } else {
                    self.right = b_right;
                }
            }
            b'f' => {
                let vacant_size1 = op2.left.wrapping_add(self.mask.wrapping_sub(a_right)).wrapping_add(1);
                let vacant_size2 = self.left.wrapping_sub(b_right);
                if vacant_size1 < vacant_size2 {
                    self.right = b_right;
                } else {
                    self.left = op2.left;
                    self.right = a_right;
                }
            }
            b'b' => {
                self.right = b_right;
            }
            b'c' => {
                self.right = a_right;
            }
            b'd' => {
                self.left = op2.left;
                self.right = b_right;
            }
            b'e' => {
                self.left = op2.left;
                self.right = a_right;
            }
            b'g' => {
                self.left = 0;
                self.right = 0;
            }
            _ => {}
        }
        self.normalize();
        self.left == self.right
    }

    pub fn invert(&mut self) -> i32 {
        let res = self.step;
        self.step = 1;
        self.complement();
        res
    }

    pub fn set_stride(&mut self, new_step: i32, rem: u64) {
        let iseverything = (!self.isempty) && (self.left == self.right);
        if new_step == self.step {
            return;
        }
        let mut a_right = self.right.wrapping_sub(step_value(self.step));
        self.step = new_step;
        if self.step == 1 {
            return;
        }
        let step = step_value(self.step);
        let mut cur_rem = self.left % step;
        self.left = self.left.wrapping_sub(cur_rem).wrapping_add(rem);
        cur_rem = a_right % step;
        a_right = a_right.wrapping_sub(cur_rem).wrapping_add(rem);
        self.right = a_right.wrapping_add(step);
        if (!iseverything) && (self.left == self.right) {
            self.isempty = true;
        }
    }

    pub fn pull_back_unary(&mut self, opc: OpCode, in_size: i32, out_size: i32) -> bool {
        if self.isempty {
            return true;
        }
        let step = step_value(self.step);
        match opc {
            OpCode::BoolNegate => {
                if self.convert_to_boolean() {
                    return true;
                }
                self.left ^= 1;
                self.right = self.left.wrapping_add(1);
            }
            OpCode::Copy => {}
            OpCode::Int2comp => {
                let val = (!self.left).wrapping_add(1).wrapping_add(step) & self.mask;
                self.left = (!self.right).wrapping_add(1).wrapping_add(step) & self.mask;
                self.right = val;
            }
            OpCode::IntNegate => {
                let val = (!self.left).wrapping_add(step) & self.mask;
                self.left = (!self.right).wrapping_add(step) & self.mask;
                self.right = val;
            }
            OpCode::IntZext => {
                let val = calc_mask(in_size);
                let rem = self.left % step;
                let zextrange = CircleRange {
                    left: rem,
                    right: val.wrapping_add(1).wrapping_add(rem),
                    mask: self.mask,
                    step: self.step,
                    isempty: false,
                };
                if 0 != self.intersect(&zextrange) {
                    return false;
                }
                self.left &= val;
                self.right &= val;
                self.mask &= val;
            }
            OpCode::IntSext => {
                let val = calc_mask(in_size);
                let rem = self.left & step;
                let mut sextrange = CircleRange {
                    left: val ^ (val >> 1),
                    right: 0,
                    mask: self.mask,
                    step: self.step,
                    isempty: false,
                };
                sextrange.left = sextrange.left.wrapping_add(rem);
                sextrange.right = sign_extend_size(sextrange.left, in_size, out_size);
                let current = self.clone();
                if sextrange.intersect(&current) != 0 || !sextrange.is_empty() {
                    return false;
                }
                self.left &= val;
                self.right &= val;
                self.mask &= val;
            }
            _ => return false,
        }
        true
    }

    pub fn pull_back_binary(&mut self, opc: OpCode, val: u64, slot: i32, in_size: i32, _out_size: i32) -> bool {
        if self.isempty {
            return true;
        }
        match opc {
            OpCode::IntEqual => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                self.left = val;
                self.right = val.wrapping_add(1) & self.mask;
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntNotequal => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                self.left = val.wrapping_add(1) & self.mask;
                self.right = val;
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntLess => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                if slot == 0 {
                    if val == 0 {
                        self.isempty = true;
                    } else {
                        self.left = 0;
                        self.right = val;
                    }
                } else if val == self.mask {
                    self.isempty = true;
                } else {
                    self.left = val.wrapping_add(1) & self.mask;
                    self.right = 0;
                }
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntLessequal => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                if slot == 0 {
                    self.left = 0;
                    self.right = val.wrapping_add(1) & self.mask;
                } else {
                    self.left = val;
                    self.right = 0;
                }
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntSless => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                if slot == 0 {
                    if val == (self.mask >> 1).wrapping_add(1) {
                        self.isempty = true;
                    } else {
                        self.left = (self.mask >> 1).wrapping_add(1);
                        self.right = val;
                    }
                } else if val == (self.mask >> 1) {
                    self.isempty = true;
                } else {
                    self.left = val.wrapping_add(1) & self.mask;
                    self.right = (self.mask >> 1).wrapping_add(1);
                }
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntSlessequal => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                if slot == 0 {
                    self.left = (self.mask >> 1).wrapping_add(1);
                    self.right = val.wrapping_add(1) & self.mask;
                } else {
                    self.left = val;
                    self.right = (self.mask >> 1).wrapping_add(1);
                }
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntCarry => {
                let both_true_false = self.convert_to_boolean();
                self.mask = calc_mask(in_size);
                if both_true_false {
                    return true;
                }
                let yescomplement = self.left == 0;
                if val == 0 {
                    self.isempty = true;
                } else {
                    self.left = self.mask.wrapping_sub(val).wrapping_add(1) & self.mask;
                    self.right = 0;
                }
                if yescomplement {
                    self.complement();
                }
            }
            OpCode::IntAdd => {
                self.left = self.left.wrapping_sub(val) & self.mask;
                self.right = self.right.wrapping_sub(val) & self.mask;
            }
            OpCode::IntSub => {
                if slot == 0 {
                    self.left = self.left.wrapping_add(val) & self.mask;
                    self.right = self.right.wrapping_add(val) & self.mask;
                } else {
                    self.left = val.wrapping_sub(self.left) & self.mask;
                    self.right = val.wrapping_sub(self.right) & self.mask;
                }
            }
            OpCode::IntRight if self.step == 1 => {
                let right_bound = (calc_mask(in_size).wrapping_shr(val as u32)).wrapping_add(1);
                if ((self.left >= right_bound) && (self.right >= right_bound) && (self.left >= self.right))
                    || ((self.left == 0) && (self.right >= right_bound))
                    || (self.left == self.right)
                {
                    self.left = 0;
                    self.right = 0;
                } else {
                    if self.left > right_bound {
                        self.left = right_bound;
                    }
                    if self.right > right_bound {
                        self.right = 0;
                    }
                    self.left = self.left.wrapping_shl(val as u32) & self.mask;
                    self.right = self.right.wrapping_shl(val as u32) & self.mask;
                    if self.left == self.right {
                        self.isempty = true;
                    }
                }
            }
            OpCode::IntSright if self.step == 1 => {
                let mut rightb = calc_mask(in_size);
                let mut leftb = rightb.wrapping_shr(val.wrapping_add(1) as u32);
                rightb ^= leftb;
                leftb = leftb.wrapping_add(1);
                if ((self.left >= leftb)
                    && (self.left <= rightb)
                    && (self.right >= leftb)
                    && (self.right <= rightb)
                    && (self.left >= self.right))
                    || (self.left == self.right)
                {
                    self.left = 0;
                    self.right = 0;
                } else {
                    if (self.left > leftb) && (self.left < rightb) {
                        self.left = leftb;
                    }
                    if (self.right > leftb) && (self.right < rightb) {
                        self.right = rightb;
                    }
                    self.left = self.left.wrapping_shl(val as u32) & self.mask;
                    self.right = self.right.wrapping_shl(val as u32) & self.mask;
                    if self.left == self.right {
                        self.isempty = true;
                    }
                }
            }
            _ => return false,
        }
        true
    }

    pub fn pull_back(
        &mut self,
        op: OpId,
        const_markup: Option<&mut Option<VarnodeId>>,
        usenzmask: bool,
        data: &Funcdata,
    ) -> Option<VarnodeId> {
        let pcode_op = data.op(op);
        let res;
        if pcode_op.num_input() == 1 {
            res = pcode_op.get_in(0);
            if data.vn(res).is_constant() {
                return None;
            }
            let out_size = data
                .vn(pcode_op.get_out().expect("pull-back op has no output"))
                .get_size();
            if !self.pull_back_unary(pcode_op.code(), data.vn(res).get_size(), out_size) {
                return None;
            }
        } else if pcode_op.num_input() == 2 {
            let mut slot = 0;
            let mut input = pcode_op.get_in(slot);
            let mut constvn = pcode_op.get_in(1 - slot);
            if data.vn(input).is_constant() {
                slot = 1;
                constvn = input;
                input = pcode_op.get_in(slot);
                if data.vn(input).is_constant() {
                    return None;
                }
            } else if !data.vn(constvn).is_constant() {
                return None;
            }
            res = input;
            let val = data.vn(constvn).get_offset();
            let opc = pcode_op.code();
            let out_size = data
                .vn(pcode_op.get_out().expect("pull-back op has no output"))
                .get_size();
            if !self.pull_back_binary(opc, val, slot, data.vn(res).get_size(), out_size) {
                if usenzmask && opc == OpCode::Subpiece && val == 0 {
                    let mut msbset = mostsigbit_set(data.vn(res).get_nz_mask());
                    msbset = (msbset + 8) / 8;
                    if out_size < msbset {
                        return None;
                    } else {
                        self.mask = calc_mask(data.vn(res).get_size());
                    }
                } else {
                    return None;
                }
            }
            if let (true, Some(markup)) = (data.vn(constvn).get_symbol_entry().is_some(), const_markup) {
                *markup = Some(constvn);
            }
        } else {
            return None;
        }
        if usenzmask {
            let mut nzrange = CircleRange::new();
            if !nzrange.set_nz_mask(data.vn(res).get_nz_mask(), data.vn(res).get_size()) {
                return Some(res);
            }
            self.intersect(&nzrange);
        }
        Some(res)
    }

    pub fn push_forward_unary(&mut self, opc: OpCode, in1: &CircleRange, in_size: i32, out_size: i32) -> bool {
        if in1.isempty {
            self.isempty = true;
            return true;
        }
        match opc {
            OpCode::Cast | OpCode::Copy => {
                *self = in1.clone();
            }
            OpCode::IntZext => {
                self.isempty = false;
                self.step = in1.step;
                self.mask = calc_mask(out_size);
                if in1.left == in1.right {
                    self.left = in1.left % step_value(self.step);
                    self.right = in1.mask.wrapping_add(1).wrapping_add(self.left);
                } else {
                    self.left = in1.left;
                    self.right = in1.right.wrapping_sub(step_value(in1.step)) & in1.mask;
                    if self.right < self.left {
                        return false;
                    }
                    self.right = self.right.wrapping_add(step_value(self.step));
                }
            }
            OpCode::IntSext => {
                self.isempty = false;
                self.step = in1.step;
                self.mask = calc_mask(out_size);
                if in1.left == in1.right {
                    let rem = in1.left % step_value(self.step);
                    self.right = calc_mask(in_size) >> 1;
                    self.left = (calc_mask(out_size) ^ self.right).wrapping_add(rem);
                    self.right = self.right.wrapping_add(1).wrapping_add(rem);
                } else {
                    self.left = sign_extend_size(in1.left, in_size, out_size);
                    self.right = sign_extend_size(
                        in1.right.wrapping_sub(step_value(in1.step)) & in1.mask,
                        in_size,
                        out_size,
                    );
                    if (self.right as i64) < (self.left as i64) {
                        return false;
                    }
                    self.right = self.right.wrapping_add(step_value(self.step)) & self.mask;
                }
            }
            OpCode::Int2comp => {
                self.isempty = false;
                self.step = in1.step;
                self.mask = in1.mask;
                let step = step_value(self.step);
                self.right = (!in1.left).wrapping_add(1).wrapping_add(step) & self.mask;
                self.left = (!in1.right).wrapping_add(1).wrapping_add(step) & self.mask;
                self.normalize();
            }
            OpCode::IntNegate => {
                self.isempty = false;
                self.step = in1.step;
                self.mask = in1.mask;
                let step = step_value(self.step);
                self.left = (!in1.right).wrapping_add(step) & self.mask;
                self.right = (!in1.left).wrapping_add(step) & self.mask;
                self.normalize();
            }
            OpCode::BoolNegate | OpCode::FloatNan => {
                self.isempty = false;
                self.mask = 0xff;
                self.step = 1;
                self.left = 0;
                self.right = 2;
            }
            _ => return false,
        }
        true
    }

    pub fn push_forward_binary(
        &mut self,
        opc: OpCode,
        in1: &CircleRange,
        in2: &CircleRange,
        in_size: i32,
        out_size: i32,
        max_step: i32,
    ) -> bool {
        if in1.isempty || in2.isempty {
            self.isempty = true;
            return true;
        }
        match opc {
            OpCode::Ptrsub | OpCode::IntAdd => {
                self.isempty = false;
                self.mask = in1.mask | in2.mask;
                if in1.left == in1.right || in2.left == in2.right {
                    self.step = if in1.step < in2.step { in1.step } else { in2.step };
                    self.left = in1.left.wrapping_add(in2.left) % step_value(self.step);
                    self.right = self.left;
                } else if in2.is_single() {
                    self.step = in1.step;
                    self.left = in1.left.wrapping_add(in2.left) & self.mask;
                    self.right = in1.right.wrapping_add(in2.left) & self.mask;
                } else if in1.is_single() {
                    self.step = in2.step;
                    self.left = in2.left.wrapping_add(in1.left) & self.mask;
                    self.right = in2.right.wrapping_add(in1.left) & self.mask;
                } else {
                    self.step = if in1.step < in2.step { in1.step } else { in2.step };
                    let step = step_value(self.step);
                    let size1 = if in1.left < in1.right {
                        in1.right - in1.left
                    } else {
                        in1.mask
                            .wrapping_sub(in1.left.wrapping_sub(in1.right))
                            .wrapping_add(step_value(in1.step))
                    };
                    self.left = in1.left.wrapping_add(in2.left) & self.mask;
                    self.right = in1
                        .right
                        .wrapping_sub(step_value(in1.step))
                        .wrapping_add(in2.right)
                        .wrapping_sub(step_value(in2.step))
                        .wrapping_add(step)
                        & self.mask;
                    let sizenew = if self.left < self.right {
                        self.right - self.left
                    } else {
                        self.mask
                            .wrapping_sub(self.left.wrapping_sub(self.right))
                            .wrapping_add(step)
                    };
                    if sizenew < size1 {
                        self.right = self.left;
                    }
                    self.normalize();
                }
            }
            OpCode::IntMult => {
                self.isempty = false;
                self.mask = in1.mask | in2.mask;
                let const_val;
                if in1.is_single() {
                    const_val = in1.get_min();
                    self.step = in2.step;
                } else if in2.is_single() {
                    const_val = in2.get_min();
                    self.step = in1.step;
                } else {
                    return false;
                }
                let mut tmp = const_val as u32;
                while self.step < max_step {
                    if (tmp & 1) != 0 {
                        break;
                    }
                    self.step = self.step.wrapping_shl(1);
                    tmp >>= 1;
                }
                let whole_size = 64 - count_leading_zeros(self.mask);
                if in1.get_max_info() + in2.get_max_info() > whole_size {
                    self.left = in1.left.wrapping_mul(in2.left) % step_value(self.step);
                    self.right = self.left;
                    self.normalize();
                    return true;
                }
                let step = step_value(self.step);
                if (const_val & (self.mask ^ (self.mask >> 1))) != 0 {
                    self.left = in1
                        .right
                        .wrapping_sub(step_value(in1.step))
                        .wrapping_mul(in2.right.wrapping_sub(step_value(in2.step)))
                        & self.mask;
                    self.right = in1.left.wrapping_mul(in2.left).wrapping_add(step) & self.mask;
                } else {
                    self.left = in1.left.wrapping_mul(in2.left) & self.mask;
                    self.right = in1
                        .right
                        .wrapping_sub(step_value(in1.step))
                        .wrapping_mul(in2.right.wrapping_sub(step_value(in2.step)))
                        .wrapping_add(step)
                        & self.mask;
                }
            }
            OpCode::IntLeft => {
                if !in2.is_single() {
                    return false;
                }
                self.isempty = false;
                self.mask = in1.mask;
                self.step = in1.step;
                let sa = in2.get_min() as u32;
                let mut tmp = sa;
                while self.step < max_step && tmp > 0 {
                    self.step = self.step.wrapping_shl(1);
                    tmp -= 1;
                }
                self.left = in1.left.wrapping_shl(sa) & self.mask;
                self.right = in1.right.wrapping_shl(sa) & self.mask;
                let whole_size = 64 - count_leading_zeros(self.mask);
                if (in1.get_max_info() as u32).wrapping_add(sa) > whole_size as u32 {
                    self.right = self.left;
                    self.normalize();
                    return true;
                }
            }
            OpCode::Subpiece => {
                if !in2.is_single() {
                    return false;
                }
                self.isempty = false;
                let sa = (in2.left as i32).wrapping_mul(8);
                self.mask = calc_mask(out_size);
                self.step = if sa == 0 { in1.step } else { 1 };
                let range = in1.right.abs_diff(in1.left);
                if range == 0 || (range.wrapping_shr(sa as u32) > self.mask) {
                    self.left = 0;
                    self.right = 0;
                } else {
                    self.left = in1.left.wrapping_shr(sa as u32);
                    self.right = (in1.right.wrapping_sub(step_value(in1.step)).wrapping_shr(sa as u32))
                        .wrapping_add(step_value(self.step));
                    self.left &= self.mask;
                    self.right &= self.mask;
                    self.normalize();
                }
            }
            OpCode::IntRight => {
                if !in2.is_single() {
                    return false;
                }
                self.isempty = false;
                let sa = in2.left as i32;
                self.mask = calc_mask(out_size);
                self.step = 1;
                if in1.left < in1.right {
                    self.left = in1.left.wrapping_shr(sa as u32);
                    self.right = (in1.right.wrapping_sub(step_value(in1.step)).wrapping_shr(sa as u32)).wrapping_add(1);
                } else {
                    self.left = 0;
                    self.right = in1.mask.wrapping_shr(sa as u32);
                }
                if self.left == self.right {
                    self.right = self.left.wrapping_add(1) & self.mask;
                }
            }
            OpCode::IntSright => {
                if !in2.is_single() {
                    return false;
                }
                self.isempty = false;
                let sa = in2.left as i32;
                self.mask = calc_mask(out_size);
                self.step = 1;
                let bit_pos = 8 * in_size - 1;
                let mut val_left = sign_extend(in1.left as i64, bit_pos);
                let mut val_right = sign_extend(in1.right as i64, bit_pos);
                if val_left >= val_right {
                    val_right = (self.mask >> 1) as i64;
                    val_left = val_right.wrapping_add(1);
                    val_left = sign_extend(val_left, bit_pos);
                }
                self.left = (val_left.wrapping_shr(sa as u32)) as u64 & self.mask;
                self.right = (val_right.wrapping_sub(in1.step as i64).wrapping_shr(sa as u32)).wrapping_add(1) as u64
                    & self.mask;
                if self.left == self.right {
                    self.right = self.left.wrapping_add(1) & self.mask;
                }
            }
            OpCode::IntEqual
            | OpCode::IntNotequal
            | OpCode::IntSless
            | OpCode::IntSlessequal
            | OpCode::IntLess
            | OpCode::IntLessequal
            | OpCode::IntCarry
            | OpCode::IntScarry
            | OpCode::IntSborrow
            | OpCode::BoolXor
            | OpCode::BoolAnd
            | OpCode::BoolOr
            | OpCode::FloatEqual
            | OpCode::FloatNotequal
            | OpCode::FloatLess
            | OpCode::FloatLessequal => {
                self.isempty = false;
                self.mask = 0xff;
                self.step = 1;
                self.left = 0;
                self.right = 2;
            }
            _ => return false,
        }
        true
    }

    pub fn push_forward_trinary(
        &mut self,
        opc: OpCode,
        in1: &CircleRange,
        in2: &CircleRange,
        in3: &CircleRange,
        in_size: i32,
        out_size: i32,
        max_step: i32,
    ) -> bool {
        if opc != OpCode::Ptradd {
            return false;
        }
        let mut tmp_range = CircleRange::new();
        if !tmp_range.push_forward_binary(OpCode::IntMult, in2, in3, in_size, in_size, max_step) {
            return false;
        }
        self.push_forward_binary(OpCode::IntAdd, in1, &tmp_range, in_size, out_size, max_step)
    }

    pub fn widen(&mut self, op2: &CircleRange, left_is_stable: bool) {
        if left_is_stable {
            let step = step_value(self.step);
            let lmod = self.left % step;
            let modulus = op2.right % step;
            if modulus <= lmod {
                self.right = op2.right.wrapping_add(lmod - modulus);
            } else {
                self.right = op2.right.wrapping_sub(modulus - lmod);
            }
            self.right &= self.mask;
        } else {
            self.left = op2.left & self.mask;
        }
        self.normalize();
    }

    pub fn translate2_op(&self, opc: &mut OpCode, cval: &mut u64, cslot: &mut i32) -> i32 {
        if self.isempty {
            return 3;
        }
        if self.step != 1 {
            return 2;
        }
        if self.right == (self.left.wrapping_add(1) & self.mask) {
            *opc = OpCode::IntEqual;
            *cslot = 0;
            *cval = self.left;
            return 0;
        }
        if self.left == (self.right.wrapping_add(1) & self.mask) {
            *opc = OpCode::IntNotequal;
            *cslot = 0;
            *cval = self.right;
            return 0;
        }
        if self.left == self.right {
            return 1;
        }
        if self.left == 0 {
            *opc = OpCode::IntLess;
            *cslot = 1;
            *cval = self.right;
            return 0;
        }
        if self.right == 0 {
            *opc = OpCode::IntLess;
            *cslot = 0;
            *cval = self.left.wrapping_sub(1) & self.mask;
            return 0;
        }
        if self.left == (self.mask >> 1).wrapping_add(1) {
            *opc = OpCode::IntSless;
            *cslot = 1;
            *cval = self.right;
            return 0;
        }
        if self.right == (self.mask >> 1).wrapping_add(1) {
            *opc = OpCode::IntSless;
            *cslot = 0;
            *cval = self.left.wrapping_sub(1) & self.mask;
            return 0;
        }
        2
    }

    pub fn print_raw(&self, out: &mut String) {
        if self.isempty {
            out.push_str("(empty)");
            return;
        }
        if self.left == self.right {
            out.push_str("(full");
            if self.step != 1 {
                let _ = write!(out, ",{}", self.step);
            }
            out.push(')');
        } else if self.right == (self.left.wrapping_add(1) & self.mask) {
            let _ = write!(out, "[{:x}]", self.left);
        } else {
            let _ = write!(out, "[{:x},{:x}", self.left, self.right);
            if self.step != 1 {
                let _ = write!(out, ",{}", self.step);
            }
            out.push(')');
        }
    }
}

impl Default for CircleRange {
    fn default() -> CircleRange {
        CircleRange::new()
    }
}

impl PartialEq for CircleRange {
    fn eq(&self, op2: &CircleRange) -> bool {
        if self.isempty != op2.isempty {
            return false;
        }
        if self.isempty {
            return true;
        }
        (self.left == op2.left) && (self.right == op2.right) && (self.mask == op2.mask) && (self.step == op2.step)
    }
}

#[derive(Clone, Debug)]
pub struct Equation {
    slot: i32,
    type_code: i32,
    range: CircleRange,
}

impl Equation {
    pub fn new(slot: i32, tc: i32, rng: &CircleRange) -> Equation {
        Equation {
            slot,
            type_code: tc,
            range: rng.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ValueSet {
    pub(crate) type_code: i32,
    pub(crate) num_params: i32,
    pub(crate) count: i32,
    pub(crate) op_code: OpCode,
    pub(crate) left_is_stable: bool,
    pub(crate) right_is_stable: bool,
    pub(crate) vn: Option<VarnodeId>,
    pub(crate) range: CircleRange,
    pub(crate) equations: Vec<Equation>,
    pub(crate) part_head: Option<usize>,
    pub(crate) next: Option<usize>,
}

enum IterateStep {
    Full,
    Unchanged,
    Computed {
        res: CircleRange,
        left_is_stable: Option<bool>,
        right_is_stable: Option<bool>,
    },
}

impl ValueSet {
    pub const MAX_STEP: i32 = 32;

    fn new_empty() -> ValueSet {
        ValueSet {
            type_code: 0,
            num_params: 0,
            count: 0,
            op_code: OpCode::Max,
            left_is_stable: false,
            right_is_stable: false,
            vn: None,
            range: CircleRange::new(),
            equations: Vec::new(),
            part_head: None,
            next: None,
        }
    }

    fn does_equation_apply(&self, num: i32, slot: i32) -> bool {
        if (num as usize) < self.equations.len() {
            let equation = &self.equations[num as usize];
            if equation.slot == slot && equation.type_code == self.type_code {
                return true;
            }
        }
        false
    }

    fn set_full(&mut self, data: &Funcdata) {
        let vn = self.vn.expect("value set has no varnode");
        self.range.set_full(data.vn(vn).get_size());
        self.type_code = 0;
    }

    fn set_varnode(&mut self, vn_id: VarnodeId, t_code: i32, data: &Funcdata) {
        self.type_code = t_code;
        self.vn = Some(vn_id);
        let vn = data.vn(vn_id);
        if self.type_code != 0 {
            self.op_code = OpCode::Max;
            self.num_params = 0;
            self.range.set_range_single(0, vn.get_size());
            self.left_is_stable = true;
            self.right_is_stable = true;
        } else if vn.is_written() {
            let op = data.op(vn.get_def().expect("written varnode has no defining op"));
            self.op_code = op.code();
            if self.op_code == OpCode::Indirect {
                self.num_params = 1;
                self.op_code = OpCode::Copy;
            } else {
                self.num_params = op.num_input();
            }
            self.left_is_stable = false;
            self.right_is_stable = false;
        } else if vn.is_constant() {
            self.op_code = OpCode::Max;
            self.num_params = 0;
            self.range.set_range_single(vn.get_offset(), vn.get_size());
            self.left_is_stable = true;
            self.right_is_stable = true;
        } else {
            self.op_code = OpCode::Max;
            self.num_params = 0;
            self.type_code = 0;
            self.range.set_full(vn.get_size());
            self.left_is_stable = false;
            self.right_is_stable = false;
        }
    }

    fn add_equation(&mut self, slot: i32, tp: i32, constraint: &CircleRange) {
        let mut position = 0;
        while position < self.equations.len() {
            if self.equations[position].slot > slot {
                break;
            }
            position += 1;
        }
        self.equations.insert(position, Equation::new(slot, tp, constraint));
    }

    fn add_landmark(&mut self, tp: i32, constraint: &CircleRange) {
        let num_params = self.num_params;
        self.add_equation(num_params, tp, constraint);
    }

    pub fn get_count(&self) -> i32 {
        self.count
    }

    pub fn get_land_mark(&self) -> Option<&CircleRange> {
        self.equations
            .iter()
            .find(|equation| equation.type_code == self.type_code)
            .map(|equation| &equation.range)
    }

    pub fn get_type_code(&self) -> i32 {
        self.type_code
    }

    pub fn get_varnode(&self) -> Option<VarnodeId> {
        self.vn
    }

    pub fn get_range(&self) -> &CircleRange {
        &self.range
    }

    pub fn is_left_stable(&self) -> bool {
        self.left_is_stable
    }

    pub fn is_right_stable(&self) -> bool {
        self.right_is_stable
    }

    pub fn print_raw(&self, out: &mut String, data: &Funcdata, glb: &Architecture) {
        match self.vn {
            None => out.push_str("root"),
            Some(vn) => data.vn_print_raw(vn, out, glb),
        }
        if self.type_code == 0 {
            out.push_str(" absolute");
        } else {
            out.push_str(" stackptr");
        }
        if self.op_code == OpCode::Max {
            let vn = self.vn.expect("value set has no varnode");
            if data.vn(vn).is_constant() {
                out.push_str(" const");
            } else {
                out.push_str(" input");
            }
        } else {
            out.push(' ');
            out.push_str(get_opname(self.op_code));
        }
        out.push(' ');
        self.range.print_raw(out);
    }
}

#[derive(Clone, Debug, Default)]
pub struct Partition {
    pub(crate) start_node: Option<usize>,
    pub(crate) stop_node: Option<usize>,
    pub(crate) is_dirty: bool,
}

impl Partition {
    pub fn new() -> Partition {
        Partition {
            start_node: None,
            stop_node: None,
            is_dirty: false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ValueSetRead {
    pub(crate) type_code: i32,
    pub(crate) slot: i32,
    pub(crate) op: Option<OpId>,
    pub(crate) range: CircleRange,
    pub(crate) equation_constraint: CircleRange,
    pub(crate) equation_type_code: i32,
    pub(crate) left_is_stable: bool,
    pub(crate) right_is_stable: bool,
}

impl ValueSetRead {
    fn new() -> ValueSetRead {
        ValueSetRead {
            type_code: 0,
            slot: 0,
            op: None,
            range: CircleRange::new(),
            equation_constraint: CircleRange::new(),
            equation_type_code: 0,
            left_is_stable: false,
            right_is_stable: false,
        }
    }

    fn set_pcode_op(&mut self, read_op: OpId, slt: i32) {
        self.type_code = 0;
        self.op = Some(read_op);
        self.slot = slt;
        self.equation_type_code = -1;
    }

    fn add_equation(&mut self, slt: i32, tp: i32, constraint: &CircleRange) {
        if self.slot == slt {
            self.equation_type_code = tp;
            self.equation_constraint = constraint.clone();
        }
    }

    pub fn get_type_code(&self) -> i32 {
        self.type_code
    }

    pub fn get_range(&self) -> &CircleRange {
        &self.range
    }

    pub fn is_left_stable(&self) -> bool {
        self.left_is_stable
    }

    pub fn is_right_stable(&self) -> bool {
        self.right_is_stable
    }

    pub fn compute(&mut self, value_nodes: &[ValueSet], data: &Funcdata) {
        let op = self.op.expect("value set read has no op");
        let vn = data.op(op).get_in(self.slot);
        let value_set = &value_nodes[data.vn(vn).get_value_set().expect("varnode has no value set")];
        self.type_code = value_set.get_type_code();
        self.range = value_set.get_range().clone();
        self.left_is_stable = value_set.is_left_stable();
        self.right_is_stable = value_set.is_right_stable();
        if self.type_code == self.equation_type_code && 0 != self.range.intersect(&self.equation_constraint) {
            self.range = self.equation_constraint.clone();
        }
    }

    pub fn print_raw(&self, out: &mut String, data: &Funcdata) {
        let op = data.op(self.op.expect("value set read has no op"));
        out.push_str("Read: ");
        out.push_str(get_opname(op.code()));
        let _ = write!(out, "({})", op.get_seq_num());
        if self.type_code == 0 {
            out.push_str(" absolute ");
        } else {
            out.push_str(" stackptr ");
        }
        self.range.print_raw(out);
    }
}

pub trait Widener {
    fn determine_iteration_reset(&mut self, value_set: &ValueSet) -> i32;

    fn check_freeze(&mut self, value_set: &ValueSet) -> bool;

    fn do_widening(&mut self, value_set: &ValueSet, range: &mut CircleRange, new_range: &CircleRange) -> bool;
}

#[derive(Clone, Debug)]
pub struct WidenerFull {
    widen_iteration: i32,
    full_iteration: i32,
}

impl WidenerFull {
    pub fn new() -> WidenerFull {
        WidenerFull {
            widen_iteration: 2,
            full_iteration: 5,
        }
    }

    pub fn with_iterations(wide: i32, full: i32) -> WidenerFull {
        WidenerFull {
            widen_iteration: wide,
            full_iteration: full,
        }
    }
}

impl Default for WidenerFull {
    fn default() -> WidenerFull {
        WidenerFull::new()
    }
}

impl Widener for WidenerFull {
    fn determine_iteration_reset(&mut self, value_set: &ValueSet) -> i32 {
        if value_set.get_count() >= self.widen_iteration {
            return self.widen_iteration;
        }
        0
    }

    fn check_freeze(&mut self, value_set: &ValueSet) -> bool {
        value_set.get_range().is_full()
    }

    fn do_widening(&mut self, value_set: &ValueSet, range: &mut CircleRange, new_range: &CircleRange) -> bool {
        if value_set.get_count() < self.widen_iteration {
            *range = new_range.clone();
            return true;
        } else if value_set.get_count() == self.widen_iteration {
            if let Some(landmark) = value_set.get_land_mark() {
                let left_is_stable = range.get_min() == new_range.get_min();
                *range = new_range.clone();
                if landmark.contains_range(range) {
                    range.widen(landmark, left_is_stable);
                    return true;
                } else {
                    let mut constraint = landmark.clone();
                    constraint.invert();
                    if constraint.contains_range(range) {
                        range.widen(&constraint, left_is_stable);
                        return true;
                    }
                }
            }
        } else if value_set.get_count() < self.full_iteration {
            *range = new_range.clone();
            return true;
        }
        false
    }
}

#[derive(Clone, Debug)]
pub struct WidenerNone {
    freeze_iteration: i32,
}

impl WidenerNone {
    pub fn new() -> WidenerNone {
        WidenerNone { freeze_iteration: 3 }
    }
}

impl Default for WidenerNone {
    fn default() -> WidenerNone {
        WidenerNone::new()
    }
}

impl Widener for WidenerNone {
    fn determine_iteration_reset(&mut self, value_set: &ValueSet) -> i32 {
        if value_set.get_count() >= self.freeze_iteration {
            return self.freeze_iteration;
        }
        value_set.get_count()
    }

    fn check_freeze(&mut self, value_set: &ValueSet) -> bool {
        if value_set.get_range().is_full() {
            return true;
        }
        value_set.get_count() >= self.freeze_iteration
    }

    fn do_widening(&mut self, _value_set: &ValueSet, range: &mut CircleRange, new_range: &CircleRange) -> bool {
        *range = new_range.clone();
        true
    }
}

#[derive(Clone, Debug)]
pub struct ValueSetEdge {
    use_roots: bool,
    root_pos: i32,
    vn: Option<VarnodeId>,
    iter: usize,
}

impl ValueSetEdge {
    pub fn new(node: usize, _roots: &[usize], value_nodes: &[ValueSet], _data: &Funcdata) -> ValueSetEdge {
        let vn = value_nodes[node].get_varnode();
        ValueSetEdge {
            use_roots: vn.is_none(),
            root_pos: 0,
            vn,
            iter: 0,
        }
    }

    pub fn get_next(&mut self, roots: &[usize], data: &Funcdata) -> Option<usize> {
        let vn = match self.vn {
            None => {
                if self.use_roots && (self.root_pos as usize) < roots.len() {
                    let res = roots[self.root_pos as usize];
                    self.root_pos += 1;
                    return Some(res);
                }
                return None;
            }
            Some(vn) => vn,
        };
        let descend = data.vn(vn).descend();
        while self.iter < descend.len() {
            let op = descend[self.iter];
            self.iter += 1;
            if let Some(out_vn) = data.op(op).get_out()
                && data.vn(out_vn).is_mark()
            {
                return data.vn(out_vn).get_value_set();
            }
        }
        None
    }
}

#[derive(Clone, Debug, Default)]
pub struct ValueSetSolver {
    pub(crate) value_nodes: Vec<ValueSet>,
    pub(crate) read_nodes: BTreeMap<SeqNum, ValueSetRead>,
    pub(crate) order_partition: Partition,
    pub(crate) record_storage: Vec<Partition>,
    pub(crate) root_nodes: Vec<usize>,
    pub(crate) node_stack: Vec<usize>,
    pub(crate) depth_first_index: i32,
    pub(crate) num_iterations: i32,
    pub(crate) max_iterations: i32,
}

impl ValueSetSolver {
    fn input_value_set(op: OpId, slot: i32, data: &Funcdata) -> usize {
        data.vn(data.op(op).get_in(slot))
            .get_value_set()
            .expect("input varnode has no value set")
    }

    fn intersect_with_equation(&self, node: usize, input: usize, eq_pos: i32) -> CircleRange {
        let equation_range = &self.value_nodes[node].equations[eq_pos as usize].range;
        let mut range_copy = self.value_nodes[input].range.clone();
        if 0 != range_copy.intersect(equation_range) {
            range_copy = equation_range.clone();
        }
        range_copy
    }

    fn compute_iteration(&self, node: usize, op: OpId, data: &Funcdata) -> IterateStep {
        let value_set = &self.value_nodes[node];
        let vn_size = data.vn(value_set.vn.expect("value set has no varnode")).get_size();
        let mut res = CircleRange::new();
        let mut eq_pos: i32 = 0;
        if value_set.op_code == OpCode::Multiequal {
            for slot in 0..value_set.num_params {
                let in_set = ValueSetSolver::input_value_set(op, slot, data);
                let pieces = if value_set.does_equation_apply(eq_pos, slot) {
                    let range_copy = self.intersect_with_equation(node, in_set, eq_pos);
                    eq_pos += 1;
                    res.circle_union(&range_copy)
                } else {
                    res.circle_union(&self.value_nodes[in_set].range)
                };
                if pieces == 2 && res.minimal_container(&self.value_nodes[in_set].range, ValueSet::MAX_STEP) {
                    break;
                }
            }
            if 0 != res.circle_union(&value_set.range) {
                res.minimal_container(&value_set.range, ValueSet::MAX_STEP);
            }
            let mut left_is_stable = None;
            let mut right_is_stable = None;
            if !value_set.range.is_empty() && !res.is_empty() {
                left_is_stable = Some(value_set.range.get_min() == res.get_min());
                right_is_stable = Some(value_set.range.get_end() == res.get_end());
            }
            IterateStep::Computed {
                res,
                left_is_stable,
                right_is_stable,
            }
        } else if value_set.num_params == 1 {
            let in_set1 = ValueSetSolver::input_value_set(op, 0, data);
            let in_size = data
                .vn(self.value_nodes[in_set1].vn.expect("value set has no varnode"))
                .get_size();
            if value_set.does_equation_apply(eq_pos, 0) {
                let range_copy = self.intersect_with_equation(node, in_set1, eq_pos);
                if !res.push_forward_unary(value_set.op_code, &range_copy, in_size, vn_size) {
                    return IterateStep::Full;
                }
            } else if !res.push_forward_unary(value_set.op_code, &self.value_nodes[in_set1].range, in_size, vn_size) {
                return IterateStep::Full;
            }
            IterateStep::Computed {
                res,
                left_is_stable: Some(self.value_nodes[in_set1].left_is_stable),
                right_is_stable: Some(self.value_nodes[in_set1].right_is_stable),
            }
        } else if value_set.num_params == 2 {
            let in_set1 = ValueSetSolver::input_value_set(op, 0, data);
            let in_set2 = ValueSetSolver::input_value_set(op, 1, data);
            let in_size = data
                .vn(self.value_nodes[in_set1].vn.expect("value set has no varnode"))
                .get_size();
            if value_set.equations.is_empty() {
                if !res.push_forward_binary(
                    value_set.op_code,
                    &self.value_nodes[in_set1].range,
                    &self.value_nodes[in_set2].range,
                    in_size,
                    vn_size,
                    ValueSet::MAX_STEP,
                ) {
                    return IterateStep::Full;
                }
            } else {
                let mut range1 = self.value_nodes[in_set1].range.clone();
                let mut range2 = self.value_nodes[in_set2].range.clone();
                if value_set.does_equation_apply(eq_pos, 0) {
                    range1 = self.intersect_with_equation(node, in_set1, eq_pos);
                    eq_pos += 1;
                }
                if value_set.does_equation_apply(eq_pos, 1) {
                    range2 = self.intersect_with_equation(node, in_set2, eq_pos);
                }
                if !res.push_forward_binary(
                    value_set.op_code,
                    &range1,
                    &range2,
                    in_size,
                    vn_size,
                    ValueSet::MAX_STEP,
                ) {
                    return IterateStep::Full;
                }
            }
            IterateStep::Computed {
                res,
                left_is_stable: Some(
                    self.value_nodes[in_set1].left_is_stable && self.value_nodes[in_set2].left_is_stable,
                ),
                right_is_stable: Some(
                    self.value_nodes[in_set1].right_is_stable && self.value_nodes[in_set2].right_is_stable,
                ),
            }
        } else if value_set.num_params == 3 {
            let in_set1 = ValueSetSolver::input_value_set(op, 0, data);
            let in_set2 = ValueSetSolver::input_value_set(op, 1, data);
            let in_set3 = ValueSetSolver::input_value_set(op, 2, data);
            let in_size = data
                .vn(self.value_nodes[in_set1].vn.expect("value set has no varnode"))
                .get_size();
            let mut range1 = self.value_nodes[in_set1].range.clone();
            let mut range2 = self.value_nodes[in_set2].range.clone();
            if value_set.does_equation_apply(eq_pos, 0) {
                range1 = self.intersect_with_equation(node, in_set1, eq_pos);
                eq_pos += 1;
            }
            if value_set.does_equation_apply(eq_pos, 1) {
                range2 = self.intersect_with_equation(node, in_set2, eq_pos);
            }
            if !res.push_forward_trinary(
                value_set.op_code,
                &range1,
                &range2,
                &self.value_nodes[in_set3].range,
                in_size,
                vn_size,
                ValueSet::MAX_STEP,
            ) {
                return IterateStep::Full;
            }
            IterateStep::Computed {
                res,
                left_is_stable: Some(
                    self.value_nodes[in_set1].left_is_stable && self.value_nodes[in_set2].left_is_stable,
                ),
                right_is_stable: Some(
                    self.value_nodes[in_set1].right_is_stable && self.value_nodes[in_set2].right_is_stable,
                ),
            }
        } else {
            IterateStep::Unchanged
        }
    }

    pub fn value_set_iterate(&mut self, node: usize, widener: &mut dyn Widener, data: &Funcdata) -> bool {
        let vn = self.value_nodes[node].vn.expect("value set has no varnode");
        if !data.vn(vn).is_written() {
            return false;
        }
        if widener.check_freeze(&self.value_nodes[node]) {
            return false;
        }
        if self.value_nodes[node].count == 0 && self.value_set_compute_type_code(node, data) {
            self.value_nodes[node].set_full(data);
            return true;
        }
        self.value_nodes[node].count += 1;
        let op = data.vn(vn).get_def().expect("written varnode has no defining op");
        match self.compute_iteration(node, op, data) {
            IterateStep::Full => {
                self.value_nodes[node].set_full(data);
                true
            }
            IterateStep::Unchanged => false,
            IterateStep::Computed {
                res,
                left_is_stable,
                right_is_stable,
            } => {
                let value_set = &mut self.value_nodes[node];
                if let Some(stable) = left_is_stable {
                    value_set.left_is_stable = stable;
                }
                if let Some(stable) = right_is_stable {
                    value_set.right_is_stable = stable;
                }
                if res == value_set.range {
                    return false;
                }
                if value_set.part_head.is_some() {
                    let mut range = value_set.range.clone();
                    let widened = widener.do_widening(value_set, &mut range, &res);
                    let value_set = &mut self.value_nodes[node];
                    value_set.range = range;
                    if !widened {
                        value_set.set_full(data);
                    }
                } else {
                    value_set.range = res;
                }
                true
            }
        }
    }

    pub fn value_set_compute_type_code(&mut self, node: usize, data: &Funcdata) -> bool {
        let mut rel_count = 0;
        let mut last_type_code = 0;
        let vn = self.value_nodes[node].vn.expect("value set has no varnode");
        let op = data.vn(vn).get_def().expect("written varnode has no defining op");
        for slot in 0..self.value_nodes[node].num_params {
            let value_set = &self.value_nodes[ValueSetSolver::input_value_set(op, slot, data)];
            if value_set.type_code != 0 {
                rel_count += 1;
                last_type_code = value_set.type_code;
            }
        }
        let value_set = &mut self.value_nodes[node];
        if rel_count == 0 {
            value_set.type_code = 0;
            return false;
        }
        match value_set.op_code {
            OpCode::Ptrsub | OpCode::Ptradd | OpCode::IntAdd | OpCode::IntSub if rel_count == 1 => {
                value_set.type_code = last_type_code;
            }
            OpCode::Cast | OpCode::Copy | OpCode::Indirect | OpCode::Multiequal => {
                value_set.type_code = last_type_code;
            }
            _ => return true,
        }
        false
    }

    fn new_value_set(&mut self, vn: VarnodeId, t_code: i32, data: &mut Funcdata) {
        let index = self.value_nodes.len();
        self.value_nodes.push(ValueSet::new_empty());
        data.vn_mut(vn).set_value_set(Some(index));
        self.value_nodes[index].set_varnode(vn, t_code, data);
    }

    fn partition_prepend(value_nodes: &mut [ValueSet], vertex: usize, part: &mut Partition) {
        value_nodes[vertex].next = part.start_node;
        part.start_node = Some(vertex);
        if part.stop_node.is_none() {
            part.stop_node = Some(vertex);
        }
    }

    fn partition_prepend_partition(value_nodes: &mut [ValueSet], head: &Partition, part: &mut Partition) {
        let stop = head.stop_node.expect("partition has no stop node");
        value_nodes[stop].next = part.start_node;
        part.start_node = head.start_node;
        if part.stop_node.is_none() {
            part.stop_node = head.stop_node;
        }
    }

    fn partition_surround(&mut self, part: &mut Partition) {
        self.record_storage.push(part.clone());
        let start = part.start_node.expect("partition has no start node");
        self.value_nodes[start].part_head = Some(self.record_storage.len() - 1);
    }

    fn component(&mut self, vertex: usize, part: &mut Partition, data: &Funcdata) {
        let mut edge_iterator = ValueSetEdge::new(vertex, &self.root_nodes, &self.value_nodes, data);
        let mut succ = edge_iterator.get_next(&self.root_nodes, data);
        while let Some(successor) = succ {
            if self.value_nodes[successor].count == 0 {
                self.visit(successor, part, data);
            }
            succ = edge_iterator.get_next(&self.root_nodes, data);
        }
        ValueSetSolver::partition_prepend(&mut self.value_nodes, vertex, part);
        self.partition_surround(part);
    }

    fn visit(&mut self, vertex: usize, part: &mut Partition, data: &Funcdata) -> i32 {
        self.node_stack.push(vertex);
        self.depth_first_index += 1;
        self.value_nodes[vertex].count = self.depth_first_index;
        let mut head = self.depth_first_index;
        let mut loop_found = false;
        let mut edge_iterator = ValueSetEdge::new(vertex, &self.root_nodes, &self.value_nodes, data);
        let mut succ = edge_iterator.get_next(&self.root_nodes, data);
        while let Some(successor) = succ {
            let min = if self.value_nodes[successor].count == 0 {
                self.visit(successor, part, data)
            } else {
                self.value_nodes[successor].count
            };
            if min <= head {
                head = min;
                loop_found = true;
            }
            succ = edge_iterator.get_next(&self.root_nodes, data);
        }
        if head == self.value_nodes[vertex].count {
            self.value_nodes[vertex].count = 0x7fffffff;
            let mut element = self.node_stack.pop().expect("node stack is empty");
            if loop_found {
                while element != vertex {
                    self.value_nodes[element].count = 0;
                    element = self.node_stack.pop().expect("node stack is empty");
                }
                let mut comp_part = Partition::new();
                self.component(vertex, &mut comp_part, data);
                ValueSetSolver::partition_prepend_partition(&mut self.value_nodes, &comp_part, part);
            } else {
                ValueSetSolver::partition_prepend(&mut self.value_nodes, vertex, part);
            }
        }
        head
    }

    fn establish_topological_order(&mut self, data: &Funcdata) {
        for value_set in self.value_nodes.iter_mut() {
            value_set.count = 0;
            value_set.next = None;
            value_set.part_head = None;
        }
        let root_node = self.value_nodes.len();
        self.value_nodes.push(ValueSet::new_empty());
        self.depth_first_index = 0;
        let mut order_partition = std::mem::take(&mut self.order_partition);
        self.visit(root_node, &mut order_partition, data);
        let start = order_partition.start_node.expect("order partition has no start node");
        order_partition.start_node = self.value_nodes[start].next;
        if order_partition.stop_node == Some(root_node) {
            order_partition.stop_node = None;
        }
        self.value_nodes.pop();
        self.order_partition = order_partition;
    }

    fn generate_true_equation(
        &mut self,
        vn: Option<VarnodeId>,
        op: OpId,
        slot: i32,
        tp: i32,
        range: &CircleRange,
        data: &Funcdata,
    ) {
        match vn {
            Some(vn) => {
                let index = data.vn(vn).get_value_set().expect("varnode has no value set");
                self.value_nodes[index].add_equation(slot, tp, range);
            }
            None => {
                let seq = data.op(op).get_seq_num().clone();
                self.read_nodes
                    .entry(seq)
                    .or_insert_with(ValueSetRead::new)
                    .add_equation(slot, tp, range);
            }
        }
    }

    fn generate_false_equation(
        &mut self,
        vn: Option<VarnodeId>,
        op: OpId,
        slot: i32,
        tp: i32,
        range: &CircleRange,
        data: &Funcdata,
    ) {
        let mut false_range = range.clone();
        false_range.invert();
        self.generate_true_equation(vn, op, slot, tp, &false_range, data);
    }

    fn apply_constraints(&mut self, vn: VarnodeId, tp: i32, range: &CircleRange, cbranch: OpId, data: &Funcdata) {
        let split_point: BlockId = data.op(cbranch).get_parent().expect("branch has no parent block");
        let (true_block, false_block) = if data.op(cbranch).is_boolean_flip() {
            (
                data.block(split_point).get_false_out(),
                data.block(split_point).get_true_out(),
            )
        } else {
            (
                data.block(split_point).get_true_out(),
                data.block(split_point).get_false_out(),
            )
        };
        let true_is_restricted = data.block_restricted_by_conditional(true_block, split_point);
        let false_is_restricted = data.block_restricted_by_conditional(false_block, split_point);

        if data.vn(vn).is_written() {
            let index = data.vn(vn).get_value_set().expect("varnode has no value set");
            if self.value_nodes[index].op_code == OpCode::Multiequal {
                self.value_nodes[index].add_landmark(tp, range);
            }
        }
        let descend = data.vn(vn).descend();
        for &op in descend.iter() {
            let mut out_vn = None;
            if !data.op(op).is_mark() {
                out_vn = data.op(op).get_out();
                match out_vn {
                    None => continue,
                    Some(out) => {
                        if !data.vn(out).is_mark() {
                            continue;
                        }
                    }
                }
            }
            let mut cur_block = data.op(op).get_parent();
            let slot = data.op(op).get_slot(vn);
            if data.op(op).code() == OpCode::Multiequal {
                if cur_block == Some(true_block) {
                    if true_is_restricted || data.block(true_block).get_in(slot) == split_point {
                        self.generate_true_equation(out_vn, op, slot, tp, range, data);
                    }
                    continue;
                } else if cur_block == Some(false_block) {
                    if false_is_restricted || data.block(false_block).get_in(slot) == split_point {
                        self.generate_false_equation(out_vn, op, slot, tp, range, data);
                    }
                    continue;
                } else {
                    cur_block = Some(data.block(cur_block.expect("op has no parent block")).get_in(slot));
                }
            }
            loop {
                if cur_block == Some(true_block) {
                    if true_is_restricted {
                        self.generate_true_equation(out_vn, op, slot, tp, range, data);
                    }
                    break;
                } else if cur_block == Some(false_block) {
                    if false_is_restricted {
                        self.generate_false_equation(out_vn, op, slot, tp, range, data);
                    }
                    break;
                }
                match cur_block {
                    None => break,
                    Some(block) => {
                        if block == split_point {
                            break;
                        }
                        cur_block = data.block(block).get_immed_dom();
                    }
                }
            }
        }
    }

    fn constraints_from_path(
        &mut self,
        tp: i32,
        lift: &mut CircleRange,
        start_vn: VarnodeId,
        end_vn: VarnodeId,
        cbranch: OpId,
        data: &Funcdata,
    ) {
        let mut start_vn = start_vn;
        while start_vn != end_vn {
            let mut const_vn = None;
            let def = data.vn(start_vn).get_def().expect("path varnode has no defining op");
            match lift.pull_back(def, Some(&mut const_vn), false, data) {
                Some(vn) => start_vn = vn,
                None => return,
            }
        }
        let mut end_vn = end_vn;
        loop {
            let mut const_vn = None;
            self.apply_constraints(end_vn, tp, lift, cbranch, data);
            if !data.vn(end_vn).is_written() {
                break;
            }
            let op = data.vn(end_vn).get_def().expect("written varnode has no defining op");
            if data.op(op).is_call() || data.op(op).is_marker() {
                break;
            }
            match lift.pull_back(op, Some(&mut const_vn), false, data) {
                Some(vn) => end_vn = vn,
                None => break,
            }
            if !data.vn(end_vn).is_mark() {
                break;
            }
        }
    }

    fn constraints_from_cbranch(&mut self, cbranch: OpId, data: &Funcdata) {
        let mut vn = data.op(cbranch).get_in(1);
        while !data.vn(vn).is_mark() {
            if !data.vn(vn).is_written() {
                break;
            }
            let op = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(op).is_call() || data.op(op).is_marker() {
                break;
            }
            let num = data.op(op).num_input();
            if num == 0 || num > 2 {
                break;
            }
            vn = data.op(op).get_in(0);
            if num == 2 {
                if data.vn(vn).is_constant() {
                    vn = data.op(op).get_in(1);
                } else if !data.vn(data.op(op).get_in(1)).is_constant() {
                    self.generate_relative_constraint(op, cbranch, data);
                    return;
                }
            }
        }
        if data.vn(vn).is_mark() {
            let mut lift = CircleRange::new_bool(true);
            let start_vn = data.op(cbranch).get_in(1);
            self.constraints_from_path(0, &mut lift, start_vn, vn, cbranch, data);
        }
    }

    fn mark_dominator_chain(start: BlockId, block_list: &mut Vec<BlockId>, data: &mut Funcdata) {
        let mut cur = Some(start);
        while let Some(block) = cur {
            if data.block(block).is_mark() {
                break;
            }
            data.block_mut(block).set_mark();
            block_list.push(block);
            cur = data.block(block).get_immed_dom();
        }
    }

    fn generate_constraints(&mut self, worklist: &[VarnodeId], reads: &[OpId], data: &mut Funcdata) {
        let mut block_list: Vec<BlockId> = Vec::new();
        for &vn in worklist.iter() {
            let op = match data.vn(vn).get_def() {
                Some(op) => op,
                None => continue,
            };
            let bl = data.op(op).get_parent().expect("op has no parent block");
            if data.op(op).code() == OpCode::Multiequal {
                for slot in 0..data.block(bl).size_in() {
                    let cur_bl = data.block(bl).get_in(slot);
                    ValueSetSolver::mark_dominator_chain(cur_bl, &mut block_list, data);
                }
            } else {
                ValueSetSolver::mark_dominator_chain(bl, &mut block_list, data);
            }
        }
        for &read in reads.iter() {
            let bl = data.op(read).get_parent().expect("op has no parent block");
            ValueSetSolver::mark_dominator_chain(bl, &mut block_list, data);
        }
        for &bl in block_list.iter() {
            data.block_mut(bl).clear_mark();
        }

        let mut final_list: Vec<BlockId> = Vec::new();
        for &bl in block_list.iter() {
            for slot in 0..data.block(bl).size_in() {
                let split_point = data.block(bl).get_in(slot);
                if data.block(split_point).is_mark() {
                    continue;
                }
                if data.block(split_point).size_out() != 2 {
                    continue;
                }
                if let Some(last_op) = data.block_last_op(split_point)
                    && data.op(last_op).code() == OpCode::Cbranch
                {
                    data.block_mut(split_point).set_mark();
                    final_list.push(split_point);
                    self.constraints_from_cbranch(last_op, data);
                }
            }
        }
        for &bl in final_list.iter() {
            data.block_mut(bl).clear_mark();
        }
    }

    fn check_relative_constant(&self, vn: VarnodeId, type_code: &mut i32, value: &mut u64, data: &Funcdata) -> bool {
        *value = 0;
        let mut vn = vn;
        loop {
            if data.vn(vn).is_mark() {
                let index = data.vn(vn).get_value_set().expect("varnode has no value set");
                let value_set = &self.value_nodes[index];
                if value_set.type_code != 0 {
                    *type_code = value_set.type_code;
                    break;
                }
            }
            if !data.vn(vn).is_written() {
                return false;
            }
            let op = data.op(data.vn(vn).get_def().expect("written varnode has no defining op"));
            let opc = op.code();
            if opc == OpCode::Copy || opc == OpCode::Indirect {
                vn = op.get_in(0);
            } else if opc == OpCode::IntAdd || opc == OpCode::Ptrsub {
                let const_vn = data.vn(op.get_in(1));
                if !const_vn.is_constant() {
                    return false;
                }
                *value = value.wrapping_add(const_vn.get_offset()) & calc_mask(const_vn.get_size());
                vn = op.get_in(0);
            } else {
                return false;
            }
        }
        true
    }

    fn generate_relative_constraint(&mut self, comp_op: OpId, cbranch: OpId, data: &Funcdata) {
        let mut opc = data.op(comp_op).code();
        match opc {
            OpCode::IntLess => opc = OpCode::IntSless,
            OpCode::IntLessequal => opc = OpCode::IntSlessequal,
            OpCode::IntSless | OpCode::IntSlessequal | OpCode::IntEqual | OpCode::IntNotequal => {}
            _ => return,
        }
        let mut type_code = 0;
        let mut value = 0;
        let vn;
        let in_vn0 = data.op(comp_op).get_in(0);
        let in_vn1 = data.op(comp_op).get_in(1);
        let mut lift = CircleRange::new_bool(true);
        if self.check_relative_constant(in_vn0, &mut type_code, &mut value, data) {
            vn = in_vn1;
            if !lift.pull_back_binary(opc, value, 1, data.vn(vn).get_size(), 1) {
                return;
            }
        } else if self.check_relative_constant(in_vn1, &mut type_code, &mut value, data) {
            vn = in_vn0;
            if !lift.pull_back_binary(opc, value, 0, data.vn(vn).get_size(), 1) {
                return;
            }
        } else {
            return;
        }

        let mut end_vn = vn;
        while !data.vn(end_vn).is_mark() {
            if !data.vn(end_vn).is_written() {
                return;
            }
            let op = data.op(data.vn(end_vn).get_def().expect("written varnode has no defining op"));
            let def_opc = op.code();
            if def_opc == OpCode::Copy || def_opc == OpCode::Ptrsub {
                end_vn = op.get_in(0);
            } else if def_opc == OpCode::IntAdd {
                if !data.vn(op.get_in(1)).is_constant() {
                    return;
                }
                end_vn = op.get_in(0);
            } else {
                return;
            }
        }
        self.constraints_from_path(type_code, &mut lift, vn, end_vn, cbranch, data);
    }

    pub fn establish_value_sets(
        &mut self,
        sinks: &[VarnodeId],
        reads: &[OpId],
        stack_reg: Option<VarnodeId>,
        indirect_as_copy: bool,
        data: &mut Funcdata,
    ) {
        let mut worklist: Vec<VarnodeId> = Vec::new();
        let mut work_pos = 0;
        if let Some(stack_reg) = stack_reg {
            self.new_value_set(stack_reg, 1, data);
            data.vn_mut(stack_reg).set_mark();
            worklist.push(stack_reg);
            work_pos += 1;
            self.root_nodes
                .push(data.vn(stack_reg).get_value_set().expect("varnode has no value set"));
        }
        for &vn in sinks.iter() {
            self.new_value_set(vn, 0, data);
            data.vn_mut(vn).set_mark();
            worklist.push(vn);
        }
        while work_pos < worklist.len() {
            let vn = worklist[work_pos];
            work_pos += 1;
            let value_set = data.vn(vn).get_value_set().expect("varnode has no value set");
            if !data.vn(vn).is_written() {
                if data.vn(vn).is_constant() {
                    let lone = data.vn(vn).lone_descend().expect("constant has no single descendant");
                    if data.vn(vn).is_spacebase() || data.op(lone).num_input() == 1 {
                        self.root_nodes.push(value_set);
                    }
                } else {
                    self.root_nodes.push(value_set);
                }
                continue;
            }
            let op = data.vn(vn).get_def().expect("written varnode has no defining op");
            match data.op(op).code() {
                OpCode::Indirect => {
                    if indirect_as_copy || data.op(op).is_indirect_store() {
                        let in_vn = data.op(op).get_in(0);
                        if !data.vn(in_vn).is_mark() {
                            self.new_value_set(in_vn, 0, data);
                            data.vn_mut(in_vn).set_mark();
                            worklist.push(in_vn);
                        }
                    } else {
                        self.value_nodes[value_set].set_full(data);
                        self.root_nodes.push(value_set);
                    }
                }
                OpCode::Call
                | OpCode::Callind
                | OpCode::Callother
                | OpCode::Load
                | OpCode::New
                | OpCode::Segmentop
                | OpCode::Cpoolref
                | OpCode::FloatAdd
                | OpCode::FloatDiv
                | OpCode::FloatMult
                | OpCode::FloatSub
                | OpCode::FloatNeg
                | OpCode::FloatAbs
                | OpCode::FloatSqrt
                | OpCode::FloatInt2float
                | OpCode::FloatFloat2float
                | OpCode::FloatTrunc
                | OpCode::FloatCeil
                | OpCode::FloatFloor
                | OpCode::FloatRound => {
                    self.value_nodes[value_set].set_full(data);
                    self.root_nodes.push(value_set);
                }
                _ => {
                    for slot in 0..data.op(op).num_input() {
                        let in_vn = data.op(op).get_in(slot);
                        if data.vn(in_vn).is_mark() || data.vn(in_vn).is_annotation() {
                            continue;
                        }
                        self.new_value_set(in_vn, 0, data);
                        data.vn_mut(in_vn).set_mark();
                        worklist.push(in_vn);
                    }
                }
            }
        }
        for &op in reads.iter() {
            for slot in 0..data.op(op).num_input() {
                let vn = data.op(op).get_in(slot);
                if data.vn(vn).is_mark() {
                    let seq = data.op(op).get_seq_num().clone();
                    self.read_nodes
                        .entry(seq)
                        .or_insert_with(ValueSetRead::new)
                        .set_pcode_op(op, slot);
                    data.op_mut(op).set_mark();
                    break;
                }
            }
        }
        self.generate_constraints(&worklist, reads, data);
        for &op in reads.iter() {
            data.op_mut(op).clear_mark();
        }

        self.establish_topological_order(data);
        for &vn in worklist.iter() {
            data.vn_mut(vn).clear_mark();
        }
    }

    pub fn get_num_iterations(&self) -> i32 {
        self.num_iterations
    }

    pub fn solve(&mut self, max: i32, widener: &mut dyn Widener, data: &Funcdata) {
        self.max_iterations = max;
        self.num_iterations = 0;
        for value_set in self.value_nodes.iter_mut() {
            value_set.count = 0;
        }

        let mut component_stack: Vec<usize> = Vec::new();
        let mut cur_component: Option<usize> = None;
        let mut cur_set = self.order_partition.start_node;

        while let Some(current) = cur_set {
            self.num_iterations += 1;
            if self.num_iterations > self.max_iterations {
                break;
            }
            if let Some(head) = self.value_nodes[current].part_head
                && Some(head) != cur_component
            {
                component_stack.push(head);
                cur_component = Some(head);
                self.record_storage[head].is_dirty = false;
                let start = self.record_storage[head]
                    .start_node
                    .expect("partition has no start node");
                self.value_nodes[start].count = widener.determine_iteration_reset(&self.value_nodes[start]);
            }
            if let Some(component) = cur_component {
                if self.value_set_iterate(current, widener, data) {
                    self.record_storage[component].is_dirty = true;
                }
                if self.record_storage[component].stop_node != Some(current) {
                    cur_set = self.value_nodes[current].next;
                } else {
                    loop {
                        let component = cur_component.expect("component stack is empty");
                        if self.record_storage[component].is_dirty {
                            self.record_storage[component].is_dirty = false;
                            cur_set = self.record_storage[component].start_node;
                            if component_stack.len() > 1 {
                                let parent = component_stack[component_stack.len() - 2];
                                self.record_storage[parent].is_dirty = true;
                            }
                            break;
                        }
                        component_stack.pop();
                        if component_stack.is_empty() {
                            cur_component = None;
                            cur_set = self.value_nodes[current].next;
                            break;
                        }
                        cur_component = component_stack.last().copied();
                        let component = cur_component.expect("component stack is empty");
                        if self.record_storage[component].stop_node != Some(current) {
                            cur_set = self.value_nodes[current].next;
                            break;
                        }
                    }
                }
            } else {
                self.value_set_iterate(current, widener, data);
                cur_set = self.value_nodes[current].next;
            }
        }
        for read in self.read_nodes.values_mut() {
            read.compute(&self.value_nodes, data);
        }
    }

    pub fn value_sets(&self) -> std::slice::Iter<'_, ValueSet> {
        self.value_nodes.iter()
    }

    pub fn value_set_reads(&self) -> std::collections::btree_map::Iter<'_, SeqNum, ValueSetRead> {
        self.read_nodes.iter()
    }

    pub fn get_value_set_read(&self, seq: &SeqNum) -> &ValueSetRead {
        self.read_nodes
            .get(seq)
            .expect("missing value set read for sequence number")
    }

    pub fn dump_value_sets(&self, out: &mut String, data: &Funcdata, glb: &Architecture) {
        for value_set in self.value_nodes.iter() {
            value_set.print_raw(out, data, glb);
            out.push('\n');
        }
        for read in self.read_nodes.values() {
            read.print_raw(out, data);
            out.push('\n');
        }
    }
}
