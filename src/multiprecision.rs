use crate::error::{Error, Result};

fn leftshift(num: usize, input: &[u64], output: &mut [u64], shift_amount: i32) {
    let mut in_index = num as i32 - 1 - shift_amount / 64;
    let shift = shift_amount % 64;
    let mut out_index = num as i32 - 1;
    if shift == 0 {
        while in_index >= 0 {
            output[out_index as usize] = input[in_index as usize];
            out_index -= 1;
            in_index -= 1;
        }
        while out_index >= 0 {
            output[out_index as usize] = 0;
            out_index -= 1;
        }
    } else {
        while in_index > 0 {
            output[out_index as usize] =
                (input[in_index as usize] << shift) | (input[in_index as usize - 1] >> (64 - shift));
            out_index -= 1;
            in_index -= 1;
        }
        output[out_index as usize] = input[0] << shift;
        out_index -= 1;
        while out_index >= 0 {
            output[out_index as usize] = 0;
            out_index -= 1;
        }
    }
}

pub fn leftshift128(input: &[u64; 2], shift_amount: i32) -> [u64; 2] {
    let mut output = [0u64; 2];
    leftshift(2, input, &mut output, shift_amount);
    output
}

fn ucompare(num: usize, first: &[u64], second: &[u64]) -> i32 {
    for slot in (0..num).rev() {
        if first[slot] != second[slot] {
            return if first[slot] < second[slot] { -1 } else { 1 };
        }
    }
    0
}

pub fn uless128(first: &[u64; 2], second: &[u64; 2]) -> bool {
    ucompare(2, first, second) < 0
}

pub fn ulessequal128(first: &[u64; 2], second: &[u64; 2]) -> bool {
    ucompare(2, first, second) <= 0
}

fn add(num: usize, first: &[u64], second: &[u64], output: &mut [u64]) {
    let mut carry: u64 = 0;
    for slot in 0..num {
        let tmp = second[slot].wrapping_add(carry);
        let tmp2 = first[slot].wrapping_add(tmp);
        output[slot] = tmp2;
        carry = if tmp < second[slot] || tmp2 < tmp { 1 } else { 0 };
    }
}

pub fn add128(first: &[u64; 2], second: &[u64; 2]) -> [u64; 2] {
    let mut output = [0u64; 2];
    add(2, first, second, &mut output);
    output
}

fn subtract(num: usize, first: &[u64], second: &[u64], output: &mut [u64]) {
    let mut borrow: u64 = 0;
    for slot in 0..num {
        let tmp = second[slot].wrapping_add(borrow);
        borrow = if tmp < second[slot] || first[slot] < tmp { 1 } else { 0 };
        output[slot] = first[slot].wrapping_sub(tmp);
    }
}

pub fn subtract128(first: &[u64; 2], second: &[u64; 2]) -> [u64; 2] {
    let mut output = [0u64; 2];
    subtract(2, first, second, &mut output);
    output
}

fn split64_32(num: usize, val: &[u64], res: &mut [u32]) -> i32 {
    let mut count = 0;
    for slot in 0..num {
        let hi = (val[slot] >> 32) as u32;
        let lo = (val[slot] & 0xffffffff) as u32;
        if hi != 0 {
            count = slot as i32 * 2 + 2;
        } else if lo != 0 {
            count = slot as i32 * 2 + 1;
        }
        res[slot * 2] = lo;
        res[slot * 2 + 1] = hi;
    }
    count
}

fn pack32_64(num: usize, max: i32, output: &mut [u64], input: &[u32]) {
    let mut pos = num as i32 * 2 - 1;
    for slot in (0..num).rev() {
        let mut val: u64 = if pos < max { input[pos as usize] as u64 } else { 0 };
        val <<= 32;
        pos -= 1;
        if pos < max {
            val |= input[pos as usize] as u64;
        }
        pos -= 1;
        output[slot] = val;
    }
}

fn shift_left(arr: &mut [u32], size: usize, shift: u32) {
    if shift == 0 {
        return;
    }
    for slot in (1..size).rev() {
        arr[slot] = (arr[slot] << shift) | (arr[slot - 1] >> (32 - shift));
    }
    arr[0] <<= shift;
}

fn shift_right(arr: &mut [u32], size: usize, shift: u32) {
    if shift == 0 {
        return;
    }
    for slot in 0..size - 1 {
        arr[slot] = (arr[slot] >> shift) | (arr[slot + 1] << (32 - shift));
    }
    arr[size - 1] >>= shift;
}

fn knuth_algorithm_d(numer_len: usize, denom_len: usize, numer: &mut [u32], denom: &mut [u32], quotient: &mut [u32]) {
    let shift = (denom[denom_len - 1] as u64).leading_zeros() - 32;
    shift_left(denom, denom_len, shift);
    shift_left(numer, numer_len, shift);

    let top = denom[denom_len - 1] as u64;
    for position in (0..(numer_len - denom_len)).rev() {
        let mut tmp: u64 =
            ((numer[denom_len + position] as u64) << 32).wrapping_add(numer[denom_len - 1 + position] as u64);
        let mut qhat = tmp / top;
        let mut rhat = tmp % top;
        loop {
            if qhat <= 0xffffffff
                && qhat.wrapping_mul(denom[denom_len - 2] as u64)
                    <= (rhat << 32).wrapping_add(numer[denom_len - 2 + position] as u64)
            {
                break;
            }
            qhat = qhat.wrapping_sub(1);
            rhat = rhat.wrapping_add(top);
            if rhat > 0xffffffff {
                break;
            }
        }

        let mut carry: u64 = 0;
        let mut signed_tmp: i64;
        for slot in 0..denom_len {
            tmp = qhat.wrapping_mul(denom[slot] as u64);
            signed_tmp = (numer[slot + position] as u64)
                .wrapping_sub(carry)
                .wrapping_sub(tmp & 0xffffffff) as i64;
            numer[slot + position] = signed_tmp as u32;
            carry = (tmp >> 32).wrapping_sub((signed_tmp >> 32) as u64);
        }
        signed_tmp = (numer[position + denom_len] as u64).wrapping_sub(carry) as i64;
        numer[position + denom_len] = signed_tmp as u32;

        quotient[position] = qhat as u32;
        if signed_tmp < 0 {
            quotient[position] = quotient[position].wrapping_sub(1);
            carry = 0;
            for slot in 0..denom_len {
                tmp = (numer[slot + position] as u64).wrapping_add((denom[slot] as u64).wrapping_add(carry));
                numer[slot + position] = tmp as u32;
                carry = tmp >> 32;
            }
            numer[position + denom_len] = numer[position + denom_len].wrapping_add(carry as u32);
        }
    }
    shift_right(numer, numer_len, shift);
}

pub fn udiv128(numer: &[u64; 2], denom: &[u64; 2]) -> Result<([u64; 2], [u64; 2])> {
    if numer[1] == 0 && denom[1] == 0 {
        if denom[0] == 0 {
            return Err(Error::Lowlevel("divide by 0".to_string()));
        }
        return Ok(([numer[0] / denom[0], 0], [numer[0] % denom[0], 0]));
    }
    let mut denom_words = [0u32; 4];
    let mut numer_words = [0u32; 5];
    let mut quotient_words = [0u32; 4];
    let denom_len = split64_32(2, denom, &mut denom_words);
    if denom_len == 0 {
        return Err(Error::Lowlevel("divide by 0".to_string()));
    }
    let mut numer_len = split64_32(2, numer, &mut numer_words);
    if numer_len < denom_len
        || (denom_len == numer_len && numer_words[denom_len as usize - 1] < denom_words[denom_len as usize - 1])
    {
        return Ok(([0, 0], [numer[0], numer[1]]));
    }
    if denom_len == 1 {
        let divisor = denom_words[0] as u64;
        let mut rem: u64 = 0;
        for slot in (0..numer_len as usize).rev() {
            let tmp = (rem << 32) + numer_words[slot] as u64;
            quotient_words[slot] = (tmp / divisor) as u32;
            numer_words[slot] = 0;
            rem = tmp % divisor;
        }
        numer_words[0] = rem as u32;
    } else {
        numer_words[numer_len as usize] = 0;
        numer_len += 1;
        knuth_algorithm_d(
            numer_len as usize,
            denom_len as usize,
            &mut numer_words,
            &mut denom_words,
            &mut quotient_words,
        );
        numer_len -= 1;
    }
    let mut quotient = [0u64; 2];
    let mut remainder = [0u64; 2];
    pack32_64(2, numer_len - denom_len + 1, &mut quotient, &quotient_words);
    pack32_64(2, numer_len, &mut remainder, &numer_words);
    Ok((quotient, remainder))
}

pub fn set_u128(val: u64) -> [u64; 2] {
    [val, 0]
}
