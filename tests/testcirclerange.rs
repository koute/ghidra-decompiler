use std::collections::BTreeSet;
use std::sync::OnceLock;

use ghidra_decompiler::address::calc_mask;
use ghidra_decompiler::error::Error;
use ghidra_decompiler::float::FloatFormat;
use ghidra_decompiler::opbehavior::{OpBehaviorRef, build_behaviors};
use ghidra_decompiler::opcodes::OpCode;
use ghidra_decompiler::rangeutil::CircleRange;

fn behaviors() -> &'static Vec<Option<OpBehaviorRef>> {
    static TABLE: OnceLock<Vec<Option<OpBehaviorRef>>> = OnceLock::new();
    TABLE.get_or_init(|| build_behaviors(&[FloatFormat::new(4), FloatFormat::new(8)]))
}

fn behavior(opcode: OpCode) -> &'static OpBehaviorRef {
    behaviors()[opcode.index()].as_ref().expect("missing behavior")
}

struct CircleRangeTest {
    elements: Vec<u64>,
    mask: u64,
    bytes: i32,
}

impl CircleRangeTest {
    fn with_size(size: i32) -> CircleRangeTest {
        CircleRangeTest {
            elements: Vec::new(),
            mask: calc_mask(size),
            bytes: size,
        }
    }

    fn from_range(range: &CircleRange) -> CircleRangeTest {
        let mask = range.get_mask();
        let mut elements = Vec::new();
        if !range.is_empty() {
            let mut start = range.get_min();
            loop {
                elements.push(start);
                if !range.get_next(&mut start) {
                    break;
                }
            }
        }
        let mut temp = mask.wrapping_add(1);
        let bytes = if temp == 0 {
            8
        } else {
            let mut count = -1;
            while temp != 0 {
                temp >>= 1;
                count += 1;
            }
            count / 8
        };
        CircleRangeTest { elements, mask, bytes }
    }

    fn set_intersect(&mut self, op2: &CircleRangeTest) {
        let first: BTreeSet<u64> = self.elements.iter().copied().collect();
        let second: BTreeSet<u64> = op2.elements.iter().copied().collect();
        self.elements = first.intersection(&second).copied().collect();
    }

    fn set_union(&mut self, op2: &CircleRangeTest) {
        let first: BTreeSet<u64> = self.elements.iter().copied().collect();
        let second: BTreeSet<u64> = op2.elements.iter().copied().collect();
        self.elements = first.union(&second).copied().collect();
    }

    fn push_unary(&mut self, opcode: OpCode, outsize: i32) {
        let behave = behavior(opcode);
        for element in self.elements.iter_mut() {
            *element = behave
                .evaluate_unary(outsize, self.bytes, *element)
                .expect("unary evaluation failed");
        }
        if outsize != self.bytes {
            self.bytes = outsize;
            self.mask = calc_mask(outsize);
        }
    }

    fn push_binary(&mut self, opcode: OpCode, outsize: i32, in1: &CircleRangeTest, in2: &CircleRangeTest) {
        let behave = behavior(opcode);
        self.elements.clear();
        for &first in in1.elements.iter() {
            for &second in in2.elements.iter() {
                self.elements.push(
                    behave
                        .evaluate_binary(outsize, in1.bytes, first, second)
                        .expect("binary evaluation failed"),
                );
            }
        }
        if outsize != self.bytes {
            self.bytes = outsize;
            self.mask = calc_mask(outsize);
        }
    }

    fn pullback_unary(&mut self, opcode: OpCode, insize: i32) {
        let behave = behavior(opcode);
        let mut res = Vec::new();
        for &element in self.elements.iter() {
            match behave.recover_input_unary(self.bytes, element, insize) {
                Ok(value) => res.push(value),
                Err(Error::Evaluation(_)) => {}
                Err(other) => panic!("unexpected recovery error: {:?}", other),
            }
        }
        self.elements = res;
        if insize != self.bytes {
            self.bytes = insize;
            self.mask = calc_mask(insize);
        }
    }

    fn pullback_binary(&mut self, opcode: OpCode, slot: i32, val: u64) {
        let behave = behavior(opcode);
        let mut res = Vec::new();
        for &element in self.elements.iter() {
            match behave.recover_input_binary(slot, self.bytes, element, self.bytes, val) {
                Ok(value) => res.push(value),
                Err(Error::Evaluation(_)) => {}
                Err(other) => panic!("unexpected recovery error: {:?}", other),
            }
        }
        self.elements = res;
    }

    fn get_start_stop_step(&mut self, start: &mut u64, stop: &mut u64, step: &mut i32) -> bool {
        if self.elements.is_empty() {
            *start = 0;
            *stop = 0;
            *step = 1;
            return true;
        }
        self.elements.sort_unstable();
        self.elements.dedup();
        let mask = self.mask;
        if *self.elements.last().expect("elements are empty") > mask {
            return false;
        }
        let elements = &self.elements;
        if elements.len() == 1 {
            *start = elements[0];
            *stop = start.wrapping_add(1) & mask;
            *step = 1;
            return true;
        }
        if elements.len() == 2 {
            let diff = elements[0].wrapping_sub(elements[1]) & mask;
            if diff == 1 || diff == 2 || diff == 4 || diff == 8 {
                *start = elements[1];
                *stop = start.wrapping_add(diff).wrapping_add(diff) & mask;
                *step = diff as i32;
                return true;
            }
        }
        let mut bigpos: i32 = -1;
        let mut biggest1: u64 = 0;
        let mut biggest2: u64 = 0;
        for index in 1..elements.len() {
            let diff = elements[index] - elements[index - 1];
            if diff >= biggest1 {
                if diff > biggest1 {
                    biggest2 = biggest1;
                    biggest1 = diff;
                    bigpos = index as i32;
                }
            } else if diff > biggest2 {
                biggest2 = diff;
            }
        }
        if biggest1 == 0 {
            return false;
        }
        if biggest2 == 0 {
            *step = biggest1 as i32;
            *start = elements[0];
            *stop = elements.last().expect("elements are empty").wrapping_add(biggest1) & mask;
            return true;
        }
        let mut count1 = 0;
        let mut count3 = 0;
        for index in 1..elements.len() {
            let diff = elements[index] - elements[index - 1];
            if diff == biggest1 {
                count1 += 1;
            } else if diff != biggest2 {
                count3 += 1;
            }
        }
        if count3 > 0 {
            return false;
        }
        if count1 > 1 {
            return false;
        }
        *step = biggest2 as i32;
        let mut tmp = elements.last().expect("elements are empty").wrapping_add(biggest2);
        if tmp <= mask {
            return false;
        }
        tmp = tmp.wrapping_sub(mask.wrapping_add(1));
        if tmp != elements[0] {
            return false;
        }
        *start = elements[bigpos as usize];
        *stop = elements[bigpos as usize - 1].wrapping_add(biggest2);
        true
    }

    fn test_equal(&mut self, valid: bool, range: &CircleRange) -> bool {
        if self.elements.is_empty() {
            return range.is_empty();
        } else if range.is_empty() {
            return false;
        }
        let mut start = 0;
        let mut stop = 0;
        let mut step = 0;
        let testvalid = self.get_start_stop_step(&mut start, &mut stop, &mut step);
        if testvalid != valid {
            return false;
        }
        if !valid {
            return true;
        }
        start == range.get_min() && stop == range.get_end() && step == range.get_step()
    }

    fn test_intersect(start1: u64, stop1: u64, start2: u64, stop2: u64, step: i32, bytes: i32) -> bool {
        let mut range1 = CircleRange::new_range(start1, stop1, bytes, step);
        let range2 = CircleRange::new_range(start2, stop2, bytes, step);
        let mut testrange1 = CircleRangeTest::from_range(&range1);
        let testrange2 = CircleRangeTest::from_range(&range2);
        let code = range1.intersect(&range2);
        testrange1.set_intersect(&testrange2);
        testrange1.test_equal(code == 0, &range1)
    }

    fn test_union(start1: u64, stop1: u64, start2: u64, stop2: u64, step: i32, bytes: i32) -> bool {
        let mut range1 = CircleRange::new_range(start1, stop1, bytes, step);
        let range2 = CircleRange::new_range(start2, stop2, bytes, step);
        let mut testrange1 = CircleRangeTest::from_range(&range1);
        let testrange2 = CircleRangeTest::from_range(&range2);
        let code = range1.circle_union(&range2);
        testrange1.set_union(&testrange2);
        testrange1.test_equal(code == 0, &range1)
    }

    fn test_pullback_unary(start: u64, stop: u64, step: i32, bytes: i32, opcode: OpCode, insize: i32) -> bool {
        let mut range = CircleRange::new_range(start, stop, bytes, step);
        let mut testrange = CircleRangeTest::from_range(&range);
        let valid = range.pull_back_unary(opcode, insize, bytes);
        testrange.pullback_unary(opcode, insize);
        testrange.test_equal(valid, &range)
    }

    fn test_pullback_binary(start: u64, stop: u64, step: i32, bytes: i32, opcode: OpCode, slot: i32, val: u64) -> bool {
        let mut range = CircleRange::new_range(start, stop, bytes, step);
        let mut testrange = CircleRangeTest::from_range(&range);
        let valid = range.pull_back_binary(opcode, val, slot, bytes, bytes);
        testrange.pullback_binary(opcode, slot, val);
        testrange.test_equal(valid, &range)
    }

    fn test_push_unary(start: u64, stop: u64, step: i32, bytes: i32, opcode: OpCode, outsize: i32) -> bool {
        let range = CircleRange::new_range(start, stop, bytes, step);
        let mut res = CircleRange::new();
        let mut testrange = CircleRangeTest::from_range(&range);
        let valid = res.push_forward_unary(opcode, &range, bytes, outsize);
        testrange.push_unary(opcode, outsize);
        testrange.test_equal(valid, &res)
    }

    #[allow(clippy::too_many_arguments)]
    fn test_push_binary(
        start1: u64,
        stop1: u64,
        step1: i32,
        start2: u64,
        stop2: u64,
        step2: i32,
        bytes: i32,
        opcode: OpCode,
        outsize: i32,
    ) -> bool {
        let range1 = CircleRange::new_range(start1, stop1, bytes, step1);
        let range2 = CircleRange::new_range(start2, stop2, bytes, step2);
        let testrange1 = CircleRangeTest::from_range(&range1);
        let testrange2 = CircleRangeTest::from_range(&range2);
        let mut res = CircleRange::new();
        let valid = res.push_forward_binary(opcode, &range1, &range2, bytes, outsize, 32);
        let mut testres = CircleRangeTest::with_size(outsize);
        testres.push_binary(opcode, outsize, &testrange1, &testrange2);
        testres.test_equal(valid, &res)
    }
}

#[test]
fn circlerange_intersect() {
    assert!(CircleRangeTest::test_intersect(1, 20, 10, 30, 1, 4));
    assert!(CircleRangeTest::test_intersect(200, 10, 250, 5, 1, 1));
    assert!(CircleRangeTest::test_intersect(1, 250, 240, 5, 1, 1));
    assert!(CircleRangeTest::test_intersect(4, 100, 248, 52, 4, 1));
    assert!(CircleRangeTest::test_intersect(
        0x100000,
        0x1000fe,
        0xfffffffffffffff0,
        0xfffffffffffffffe,
        2,
        8
    ));
    assert!(CircleRangeTest::test_intersect(0x100, 0x110, 0x110, 0x130, 4, 2));
    assert!(CircleRangeTest::test_intersect(0xffe0, 0x20, 0, 0x20, 2, 2));
    assert!(CircleRangeTest::test_intersect(0x80, 0x8, 0xd0, 0x80, 1, 1));
}

#[test]
fn circlerange_union() {
    assert!(CircleRangeTest::test_union(1, 20, 10, 30, 1, 4));
    assert!(CircleRangeTest::test_union(200, 10, 250, 5, 1, 1));
    assert!(CircleRangeTest::test_union(1, 250, 240, 5, 1, 1));
    assert!(CircleRangeTest::test_union(4, 100, 248, 52, 4, 1));
    assert!(CircleRangeTest::test_union(
        0x100000,
        0x1000fe,
        0xfffffffffffffff0,
        0xfffffffffffffffe,
        2,
        8
    ));
    assert!(CircleRangeTest::test_union(0x100, 0x110, 0x110, 0x130, 4, 2));
    assert!(CircleRangeTest::test_union(0xffe0, 0x20, 0, 0x20, 2, 2));
    assert!(CircleRangeTest::test_union(0x80, 0x8, 0xd0, 0x80, 1, 1));
}

#[test]
fn circlerange_pullback_negate() {
    assert!(CircleRangeTest::test_pullback_unary(1, 20, 1, 4, OpCode::IntNegate, 4));
    assert!(CircleRangeTest::test_pullback_unary(
        0xf0,
        0x10,
        1,
        1,
        OpCode::IntNegate,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0x10,
        0x30,
        4,
        4,
        OpCode::IntNegate,
        4
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::IntNegate,
        2
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xd1,
        0x11,
        4,
        1,
        OpCode::IntNegate,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0,
        0x30,
        4,
        1,
        OpCode::IntNegate,
        1
    ));
}

#[test]
fn circlerange_pullback_minus() {
    assert!(CircleRangeTest::test_pullback_unary(1, 20, 1, 4, OpCode::Int2comp, 4));
    assert!(CircleRangeTest::test_pullback_unary(
        0xf0,
        0x10,
        1,
        1,
        OpCode::Int2comp,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0x10,
        0x30,
        4,
        4,
        OpCode::Int2comp,
        4
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::Int2comp,
        2
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xd1,
        0x11,
        4,
        1,
        OpCode::Int2comp,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(0, 0x30, 4, 1, OpCode::Int2comp, 1));
}

#[test]
fn circlerange_pullback_zext() {
    assert!(CircleRangeTest::test_pullback_unary(1, 20, 1, 4, OpCode::IntZext, 2));
    assert!(CircleRangeTest::test_pullback_unary(
        0xfff0,
        0xff10,
        1,
        2,
        OpCode::IntZext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0x10,
        0x30,
        4,
        4,
        OpCode::IntZext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::IntZext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xffd1,
        0x11,
        4,
        2,
        OpCode::IntZext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(0, 0x30, 4, 4, OpCode::IntZext, 2));
}

#[test]
fn circlerange_pullback_sext() {
    assert!(CircleRangeTest::test_pullback_unary(1, 20, 1, 4, OpCode::IntSext, 2));
    assert!(CircleRangeTest::test_pullback_unary(
        0xfff0,
        0x10,
        1,
        2,
        OpCode::IntSext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0x10,
        0x30,
        4,
        4,
        OpCode::IntSext,
        2
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::IntSext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(
        0xffd1,
        0x11,
        4,
        2,
        OpCode::IntSext,
        1
    ));
    assert!(CircleRangeTest::test_pullback_unary(0, 0x30, 4, 2, OpCode::IntSext, 1));
}

#[test]
fn circlerange_pullback_add() {
    assert!(CircleRangeTest::test_pullback_binary(
        1,
        20,
        1,
        4,
        OpCode::IntAdd,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0xf0,
        0x10,
        1,
        1,
        OpCode::IntAdd,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0x10,
        0x30,
        4,
        4,
        OpCode::IntAdd,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::IntAdd,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0xd1,
        0x11,
        4,
        1,
        OpCode::IntAdd,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0,
        0x30,
        4,
        1,
        OpCode::IntAdd,
        0,
        0xfffffffd
    ));
}

#[test]
fn circlerange_pullback_sub() {
    assert!(CircleRangeTest::test_pullback_binary(
        1,
        20,
        1,
        4,
        OpCode::IntSub,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0xf0,
        0x10,
        1,
        1,
        OpCode::IntSub,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0x10,
        0x30,
        4,
        4,
        OpCode::IntSub,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::IntSub,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0xd1,
        0x11,
        4,
        1,
        OpCode::IntSub,
        0,
        0xfffffffd
    ));
    assert!(CircleRangeTest::test_pullback_binary(
        0,
        0x30,
        4,
        1,
        OpCode::IntSub,
        0,
        0xfffffffd
    ));
}

#[test]
fn circlerange_pullback_right() {
    let mut range = CircleRange::new_range(0x01, 0x0f, 2, 1);
    assert!(range.pull_back_binary(OpCode::IntRight, 8, 0, 2, 2));
    assert_eq!(range.get_min(), 0x100);
    assert_eq!(range.get_end(), 0xf00);

    let mut range = CircleRange::new_range(0xf0, 0x10, 2, 1);
    assert!(range.pull_back_binary(OpCode::IntRight, 8, 0, 2, 2));
    assert_eq!(range.get_min(), 0xf000);
    assert_eq!(range.get_end(), 0x1000);

    let mut range = CircleRange::new_range(0xf0, 0x10, 1, 1);
    assert!(range.pull_back_binary(OpCode::IntRight, 1, 0, 1, 1));
    assert_eq!(0, range.get_min());
    assert_eq!(0x20, range.get_end());

    let mut range = CircleRange::new_range(0x01, 0x0f, 2, 2);
    assert!(!range.pull_back_binary(OpCode::IntRight, 8, 0, 2, 2));
}

#[test]
fn circlerange_pullback_sright() {
    let mut range = CircleRange::new_range(0x01, 0x0f, 2, 1);
    assert!(range.pull_back_binary(OpCode::IntSright, 8, 0, 2, 2));
    assert_eq!(range.get_min(), 0x100);
    assert_eq!(range.get_end(), 0xf00);

    let mut range = CircleRange::new_range(0xf0, 0x10, 1, 1);
    assert!(range.pull_back_binary(OpCode::IntSright, 2, 0, 1, 1));
    assert_eq!(range.get_min(), 0xc0);
    assert_eq!(range.get_end(), 0x40);

    let mut range = CircleRange::new_range(0x10, 0x30, 1, 1);
    assert!(range.pull_back_binary(OpCode::IntSright, 2, 0, 1, 1));
    assert_eq!(range.get_min(), 0x40);
    assert_eq!(range.get_end(), 0x80);

    let mut range = CircleRange::new_range(0x01, 0x0f, 2, 2);
    assert!(!range.pull_back_binary(OpCode::IntSright, 8, 0, 2, 2));
}

fn check_bool_pullback(start_value: bool, opcode: OpCode, val: u64, in_size: i32, min: u64, end: u64) {
    let mut range = CircleRange::new_bool(start_value);
    assert!(range.pull_back_binary(opcode, val, 0, in_size, 1));
    assert_eq!(range.get_min(), min);
    assert_eq!(range.get_end(), end);
}

#[test]
fn circlerange_pullback_comparisons() {
    check_bool_pullback(true, OpCode::IntEqual, 0x1234, 4, 0x1234, 0x1235);
    check_bool_pullback(false, OpCode::IntEqual, 0x1234, 2, 0x1235, 0x1234);
    check_bool_pullback(false, OpCode::IntNotequal, 0x1234, 4, 0x1234, 0x1235);
    check_bool_pullback(true, OpCode::IntNotequal, 0x1234, 2, 0x1235, 0x1234);
    check_bool_pullback(true, OpCode::IntCarry, 0x1234, 2, 0xedcc, 0);
    check_bool_pullback(false, OpCode::IntCarry, 0x1234, 2, 0, 0xedcc);
    check_bool_pullback(false, OpCode::IntLess, 0x1234, 4, 0x1234, 0);
    check_bool_pullback(true, OpCode::IntLess, 0x1234, 2, 0, 0x1234);
    check_bool_pullback(false, OpCode::IntLessequal, 0x1234, 4, 0x1235, 0);
    check_bool_pullback(true, OpCode::IntLessequal, 0x1234, 2, 0, 0x1235);
    check_bool_pullback(false, OpCode::IntSless, 0x1234, 4, 0x1234, 0x80000000);
    check_bool_pullback(true, OpCode::IntSless, 0x1234, 2, 0x8000, 0x1234);
    check_bool_pullback(false, OpCode::IntSlessequal, 0x1234, 4, 0x1235, 0x80000000);
    check_bool_pullback(true, OpCode::IntSlessequal, 0x1234, 2, 0x8000, 0x1235);
}

#[test]
fn circlerange_push_negate() {
    assert!(CircleRangeTest::test_push_unary(1, 20, 1, 4, OpCode::IntNegate, 4));
    assert!(CircleRangeTest::test_push_unary(0xf0, 0x10, 1, 1, OpCode::IntNegate, 1));
    assert!(CircleRangeTest::test_push_unary(0x10, 0x30, 4, 4, OpCode::IntNegate, 4));
    assert!(CircleRangeTest::test_push_unary(
        0xfff0,
        0x0,
        4,
        2,
        OpCode::IntNegate,
        2
    ));
    assert!(CircleRangeTest::test_push_unary(0xd1, 0x11, 4, 1, OpCode::IntNegate, 1));
    assert!(CircleRangeTest::test_push_unary(0, 0x30, 4, 1, OpCode::IntNegate, 1));
}

#[test]
fn circlerange_push_minus() {
    assert!(CircleRangeTest::test_push_unary(1, 20, 1, 4, OpCode::Int2comp, 4));
    assert!(CircleRangeTest::test_push_unary(0xf0, 0x10, 1, 1, OpCode::Int2comp, 1));
    assert!(CircleRangeTest::test_push_unary(0x10, 0x30, 4, 4, OpCode::Int2comp, 4));
    assert!(CircleRangeTest::test_push_unary(0xfff0, 0x0, 4, 2, OpCode::Int2comp, 2));
    assert!(CircleRangeTest::test_push_unary(0xd1, 0x11, 4, 1, OpCode::Int2comp, 1));
    assert!(CircleRangeTest::test_push_unary(0, 0x30, 4, 1, OpCode::Int2comp, 1));
}

#[test]
fn circlerange_push_zext() {
    assert!(CircleRangeTest::test_push_unary(1, 20, 1, 2, OpCode::IntZext, 4));
    assert!(CircleRangeTest::test_push_unary(
        0xfff0,
        0xff10,
        1,
        2,
        OpCode::IntZext,
        4
    ));
    assert!(CircleRangeTest::test_push_unary(0x10, 0x30, 4, 2, OpCode::IntZext, 4));
    assert!(CircleRangeTest::test_push_unary(0xfff0, 0x0, 4, 2, OpCode::IntZext, 4));
    assert!(CircleRangeTest::test_push_unary(
        0xffd1,
        0xfff1,
        4,
        2,
        OpCode::IntZext,
        4
    ));
    assert!(CircleRangeTest::test_push_unary(0, 0x30, 4, 1, OpCode::IntZext, 2));
    assert!(CircleRangeTest::test_push_unary(0, 0, 4, 1, OpCode::IntZext, 2));
}

#[test]
fn circlerange_push_sext() {
    assert!(CircleRangeTest::test_push_unary(1, 20, 1, 2, OpCode::IntSext, 4));
    assert!(CircleRangeTest::test_push_unary(
        0xfff0,
        0xff10,
        1,
        2,
        OpCode::IntSext,
        4
    ));
    assert!(CircleRangeTest::test_push_unary(0x10, 0x30, 4, 2, OpCode::IntSext, 4));
    assert!(CircleRangeTest::test_push_unary(0xfff0, 0x0, 4, 2, OpCode::IntSext, 4));
    assert!(CircleRangeTest::test_push_unary(
        0xffd1,
        0xfff1,
        4,
        2,
        OpCode::IntSext,
        4
    ));
    assert!(CircleRangeTest::test_push_unary(0, 0x30, 4, 1, OpCode::IntSext, 2));
    assert!(CircleRangeTest::test_push_unary(0, 0, 4, 1, OpCode::IntSext, 2));
}

#[test]
fn circlerange_push_add() {
    assert!(CircleRangeTest::test_push_binary(
        10,
        15,
        1,
        30,
        35,
        1,
        1,
        OpCode::IntAdd,
        1
    ));
    assert!(CircleRangeTest::test_push_binary(
        1,
        10,
        1,
        0xfffffffe,
        5,
        1,
        4,
        OpCode::IntAdd,
        4
    ));
    assert!(CircleRangeTest::test_push_binary(
        0,
        20,
        4,
        0xfff0,
        6,
        2,
        2,
        OpCode::IntAdd,
        2
    ));
    assert!(CircleRangeTest::test_push_binary(
        1,
        250,
        1,
        20,
        30,
        1,
        1,
        OpCode::IntAdd,
        1
    ));
}

#[test]
fn circlerange_push_mult() {
    assert!(CircleRangeTest::test_push_binary(
        0x1000,
        0x1010,
        1,
        2,
        3,
        1,
        4,
        OpCode::IntMult,
        4
    ));
    assert!(CircleRangeTest::test_push_binary(
        0xfffc,
        8,
        2,
        4,
        5,
        1,
        2,
        OpCode::IntMult,
        2
    ));
    assert!(CircleRangeTest::test_push_binary(
        5,
        133,
        1,
        2,
        3,
        1,
        1,
        OpCode::IntMult,
        1
    ));
}

#[test]
fn circlerange_push_left() {
    assert!(CircleRangeTest::test_push_binary(
        1,
        5,
        1,
        1,
        2,
        1,
        4,
        OpCode::IntLeft,
        4
    ));
    assert!(CircleRangeTest::test_push_binary(
        8,
        72,
        4,
        2,
        3,
        1,
        1,
        OpCode::IntLeft,
        1
    ));
}

#[test]
fn circlerange_push_subpiece() {
    assert!(CircleRangeTest::test_push_binary(
        0xfffe,
        0x10005,
        1,
        0,
        1,
        1,
        4,
        OpCode::Subpiece,
        1
    ));
    assert!(CircleRangeTest::test_push_binary(
        0xfffe,
        0x10005,
        1,
        1,
        2,
        1,
        4,
        OpCode::Subpiece,
        1
    ));
    assert!(CircleRangeTest::test_push_binary(
        0x10f0,
        0x1200,
        1,
        0,
        1,
        1,
        4,
        OpCode::Subpiece,
        1
    ));
}

#[test]
fn circlerange_push_right() {
    assert!(CircleRangeTest::test_push_binary(
        0x30a6,
        0x30c0,
        2,
        4,
        5,
        1,
        2,
        OpCode::IntRight,
        2
    ));
    assert!(CircleRangeTest::test_push_binary(
        0xfe00,
        0xffc0,
        0x20,
        9,
        10,
        1,
        2,
        OpCode::IntRight,
        2
    ));
    assert!(CircleRangeTest::test_push_binary(
        7,
        10,
        1,
        4,
        5,
        1,
        4,
        OpCode::IntRight,
        4
    ));
}

#[test]
fn circlerange_push_sright() {
    assert!(CircleRangeTest::test_push_binary(
        0x3000,
        0x3064,
        4,
        3,
        4,
        1,
        2,
        OpCode::IntSright,
        2
    ));
    assert!(CircleRangeTest::test_push_binary(
        0xfff0,
        0x24,
        4,
        3,
        4,
        1,
        2,
        OpCode::IntSright,
        2
    ));
}

#[test]
fn circlerange_print_raw() {
    let mut out = String::new();
    CircleRange::new().print_raw(&mut out);
    out.push(' ');
    let mut full = CircleRange::new();
    full.set_full(4);
    full.print_raw(&mut out);
    out.push(' ');
    CircleRange::new_single(0x1f, 4).print_raw(&mut out);
    out.push(' ');
    CircleRange::new_range(0x10, 0x30, 4, 4).print_raw(&mut out);
    out.push(' ');
    CircleRange::new_range(0x10, 0x10, 4, 4).print_raw(&mut out);
    assert_eq!(out, "(empty) (full) [1f] [10,30,4) (full,4)");
}

#[test]
fn circlerange_translate2_op() {
    let mut opc = OpCode::Blank;
    let mut cval = 0;
    let mut cslot = -1;
    assert_eq!(
        CircleRange::new_range(0, 0x20, 4, 1).translate2_op(&mut opc, &mut cval, &mut cslot),
        0
    );
    assert_eq!((opc, cval, cslot), (OpCode::IntLess, 0x20, 1));
    assert_eq!(
        CircleRange::new_range(0x80000000, 0x20, 4, 1).translate2_op(&mut opc, &mut cval, &mut cslot),
        0
    );
    assert_eq!((opc, cval, cslot), (OpCode::IntSless, 0x20, 1));
    assert_eq!(
        CircleRange::new_range(0x21, 0x20, 4, 1).translate2_op(&mut opc, &mut cval, &mut cslot),
        0
    );
    assert_eq!((opc, cval, cslot), (OpCode::IntNotequal, 0x20, 0));
    assert_eq!(
        CircleRange::new_range(0x10, 0x20, 4, 4).translate2_op(&mut opc, &mut cval, &mut cslot),
        2
    );
    assert_eq!(CircleRange::new().translate2_op(&mut opc, &mut cval, &mut cslot), 3);
}
