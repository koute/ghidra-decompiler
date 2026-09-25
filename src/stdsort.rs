const SORT_THRESHOLD: usize = 16;

pub fn std_sort<T: Clone, F: FnMut(&T, &T) -> bool>(slice: &mut [T], mut less: F) {
    let len = slice.len();
    if len == 0 {
        return;
    }
    let depth_limit = 2 * (usize::BITS - 1 - len.leading_zeros()) as usize;
    introsort_loop(slice, 0, len, depth_limit, &mut less);
    final_insertion_sort(slice, 0, len, &mut less);
}

pub fn std_partial_sort_full<T: Clone, F: FnMut(&T, &T) -> bool>(slice: &mut [T], mut less: F) {
    let len = slice.len();
    heap_sort_range(slice, 0, len, &mut less);
}

fn introsort_loop<T: Clone, F: FnMut(&T, &T) -> bool>(
    slice: &mut [T],
    first: usize,
    last: usize,
    depth_limit: usize,
    less: &mut F,
) {
    let mut last = last;
    let mut depth_limit = depth_limit;
    while last - first > SORT_THRESHOLD {
        if depth_limit == 0 {
            heap_sort_range(slice, first, last, less);
            return;
        }
        depth_limit -= 1;
        let cut = unguarded_partition_pivot(slice, first, last, less);
        introsort_loop(slice, cut, last, depth_limit, less);
        last = cut;
    }
}

fn unguarded_partition_pivot<T: Clone, F: FnMut(&T, &T) -> bool>(
    slice: &mut [T],
    first: usize,
    last: usize,
    less: &mut F,
) -> usize {
    let mid = first + (last - first) / 2;
    move_median_to_first(slice, first, first + 1, mid, last - 1, less);
    unguarded_partition(slice, first + 1, last, first, less)
}

fn move_median_to_first<T: Clone, F: FnMut(&T, &T) -> bool>(
    slice: &mut [T],
    result: usize,
    first_pos: usize,
    mid_pos: usize,
    last_pos: usize,
    less: &mut F,
) {
    if less(&slice[first_pos], &slice[mid_pos]) {
        if less(&slice[mid_pos], &slice[last_pos]) {
            slice.swap(result, mid_pos);
        } else if less(&slice[first_pos], &slice[last_pos]) {
            slice.swap(result, last_pos);
        } else {
            slice.swap(result, first_pos);
        }
    } else if less(&slice[first_pos], &slice[last_pos]) {
        slice.swap(result, first_pos);
    } else if less(&slice[mid_pos], &slice[last_pos]) {
        slice.swap(result, last_pos);
    } else {
        slice.swap(result, mid_pos);
    }
}

fn unguarded_partition<T: Clone, F: FnMut(&T, &T) -> bool>(
    slice: &mut [T],
    first: usize,
    last: usize,
    pivot: usize,
    less: &mut F,
) -> usize {
    let mut first = first;
    let mut last = last;
    loop {
        while less(&slice[first], &slice[pivot]) {
            first += 1;
        }
        last -= 1;
        while less(&slice[pivot], &slice[last]) {
            last -= 1;
        }
        if first >= last {
            return first;
        }
        slice.swap(first, last);
        first += 1;
    }
}

fn final_insertion_sort<T: Clone, F: FnMut(&T, &T) -> bool>(slice: &mut [T], first: usize, last: usize, less: &mut F) {
    if last - first > SORT_THRESHOLD {
        insertion_sort(slice, first, first + SORT_THRESHOLD, less);
        for position in (first + SORT_THRESHOLD)..last {
            unguarded_linear_insert(slice, position, first, less);
        }
    } else {
        insertion_sort(slice, first, last, less);
    }
}

fn insertion_sort<T: Clone, F: FnMut(&T, &T) -> bool>(slice: &mut [T], first: usize, last: usize, less: &mut F) {
    if first == last {
        return;
    }
    for position in (first + 1)..last {
        if less(&slice[position], &slice[first]) {
            slice[first..=position].rotate_right(1);
        } else {
            unguarded_linear_insert(slice, position, first, less);
        }
    }
}

fn unguarded_linear_insert<T: Clone, F: FnMut(&T, &T) -> bool>(
    slice: &mut [T],
    last: usize,
    lower_bound: usize,
    less: &mut F,
) {
    let value = slice[last].clone();
    let mut hole = last;
    while hole > lower_bound && less(&value, &slice[hole - 1]) {
        hole -= 1;
    }
    slice[hole..=last].rotate_right(1);
}

fn adjust_heap<T: Clone, F: FnMut(&T, &T) -> bool>(
    slice: &mut [T],
    first: usize,
    hole_index: isize,
    len: isize,
    value: T,
    less: &mut F,
) {
    let top_index = hole_index;
    let mut hole_index = hole_index;
    let mut second_child = hole_index;
    while second_child < (len - 1) / 2 {
        second_child = 2 * (second_child + 1);
        if less(
            &slice[first + second_child as usize],
            &slice[first + (second_child - 1) as usize],
        ) {
            second_child -= 1;
        }
        slice[first + hole_index as usize] = slice[first + second_child as usize].clone();
        hole_index = second_child;
    }
    if (len & 1) == 0 && second_child == (len - 2) / 2 {
        second_child = 2 * (second_child + 1);
        slice[first + hole_index as usize] = slice[first + (second_child - 1) as usize].clone();
        hole_index = second_child - 1;
    }
    let mut parent = (hole_index - 1) / 2;
    while hole_index > top_index && less(&slice[first + parent as usize], &value) {
        slice[first + hole_index as usize] = slice[first + parent as usize].clone();
        hole_index = parent;
        parent = (hole_index - 1) / 2;
    }
    slice[first + hole_index as usize] = value;
}

fn heap_sort_range<T: Clone, F: FnMut(&T, &T) -> bool>(slice: &mut [T], first: usize, last: usize, less: &mut F) {
    let len = (last - first) as isize;
    if len >= 2 {
        let mut parent = (len - 2) / 2;
        loop {
            let value = slice[first + parent as usize].clone();
            adjust_heap(slice, first, parent, len, value, less);
            if parent == 0 {
                break;
            }
            parent -= 1;
        }
    }
    let mut end = last;
    while end - first > 1 {
        end -= 1;
        let value = slice[end].clone();
        slice[end] = slice[first].clone();
        adjust_heap(slice, first, 0, (end - first) as isize, value, less);
    }
}
