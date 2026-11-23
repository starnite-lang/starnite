#![allow(unused_mut, unused_variables)]
use std::{hint::black_box, io, rc::Rc, time::Instant};

struct Pair { x: i64, y: i64 }

fn data(n: i64) -> Vec<i64> {
    (0..n).map(|i| (i * 7919 + 17) % 100003).collect()
}

fn strings(seed: i64) -> Vec<String> {
    (0..128).map(|i| {
        let d = (i * 7 + seed) % 1000 + 1000;
        format!("  name{d},alpha,tag{},é漢🙂  ", d * 3)
    }).collect()
}

fn bench_int_arithmetic(seed: i64) -> (u128, i64) {
    let mut x = seed;
    let start = Instant::now();
    for _ in 0..4000000 { x = (x * 1664525 + 1013904223) % 2147483647; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, x)
}

fn bench_float_arithmetic(seed: i64) -> (u128, i64) {
    let mut x = seed as f64;
    let start = Instant::now();
    for _ in 0..4000000 { x = x * 0.9999999 + 0.000013; x /= 1.0000001; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, (x * 1000000.0) as i64)
}

fn bench_array_fill(seed: i64) -> (u128, i64) {
    let start = Instant::now();
    let a = vec![seed; 2000000];
    black_box(&a);
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a.len() as i64 + a[1000000])
}

fn bench_array_push(seed: i64) -> (u128, i64) {
    let mut a = Vec::new();
    let start = Instant::now();
    for i in 0..500000 { a.push(i + seed); }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a.len() as i64 + a[250000])
}

fn bench_array_pop(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let mut sum = 0;
    let start = Instant::now();
    for _ in 0..500000 { sum += a.pop().unwrap(); }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum + a.len() as i64)
}

fn bench_array_scan(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let mut sum = 0;
    let start = Instant::now();
    for &x in &a { sum += x; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_array_index_read(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..1000000 { sum += a[i * 7919 % 500000]; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_array_index_write(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let start = Instant::now();
    for i in 0..500000 { a[i * 7919 % 500000] = seed + i as i64; }
    black_box(&a);
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a[0] + a[333333] + a[499999])
}

fn bench_array_front_insert_remove(seed: i64) -> (u128, i64) {
    let mut a = data(16000);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..5000 { a.insert(0, i + seed); sum += a.remove(0); }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum + a[8192])
}

fn bench_array_reverse(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let start = Instant::now();
    a.reverse();
    black_box(&a);
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a[0] + 3 * a[499999])
}

fn bench_array_sort(seed: i64) -> (u128, i64) {
    let mut x = seed;
    let mut a: Vec<_> = (0..50000).map(|_| {
        x = (x * 1664525 + 1013904223) % 2147483647;
        x % 100003
    }).collect();
    let start = Instant::now();
    a.sort();
    black_box(&a);
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a[0] + a[25000] + a[49999])
}

fn bench_array_contains(seed: i64) -> (u128, i64) {
    let a = data(10000);
    let mut hits = 0;
    let start = Instant::now();
    for i in 0..1800 { if a.contains(&(i * 7919 % 100003)) { hits += 1; } }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, hits)
}

fn bench_array_owned_slice(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let start = Instant::now();
    let b = a[100000..450000].to_vec();
    black_box(&b);
    let elapsed = start.elapsed().as_nanos();
    (elapsed, b.len() as i64 + b[0] + b[349999])
}

fn bench_array_extend(seed: i64) -> (u128, i64) {
    let mut a = data(500000);
    let b = data(500000);
    let start = Instant::now();
    a.extend_from_slice(&b);
    black_box(&a);
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a.len() as i64 + a[499999] + a[500000])
}

fn bench_array_snapshot_write(seed: i64) -> (u128, i64) {
    let a = Rc::new(data(500000));
    let start = Instant::now();
    let mut b = Rc::clone(&a);
    Rc::make_mut(&mut b)[250000] = seed;
    black_box((&a, &b));
    let elapsed = start.elapsed().as_nanos();
    (elapsed, a[250000] + 3 * b[250000] + b.len() as i64)
}

fn bench_str_concat(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..200000 {
        let s = &values[i % 128];
        let out = [s.as_str(), values[(i + 1) % 128].as_str()].concat();
        black_box(&out);
        sum += (out.len() + out.as_bytes()[0] as usize) as i64;
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_owned_slice(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..200000 {
        let s = &values[i % 128];
        let out = s[0..12].to_owned();
        black_box(&out);
        sum += (out.len() + out.as_bytes()[2] as usize) as i64;
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_contains(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let needles: Vec<_> = values.iter().map(|s| &s[18..22]).collect();
    let start = Instant::now();
    for i in 0..200000 { if values[i % 128].contains(needles[(i * 7 + 13) % 128]) { sum += 1; } }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_prefix_suffix_eq(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..500000 {
        let s = &values[i % 128];
        if s.starts_with("  name") && s.ends_with("  ") && *s != values[(i + 1) % 128] { sum += 1; }
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_split_owned(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..100000 {
        let s = &values[i % 128];
        let pieces: Vec<String> = s.split(',').map(str::to_owned).collect();
        black_box(&pieces);
        sum += (pieces.len() + pieces[1].len() + pieces[2].len()) as i64;
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_join(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..150000 {
        let s = &values[i % 128];
        let out = [s.as_str(), values[(i + 1) % 128].as_str(), "end"].join("|");
        black_box(&out);
        sum += (out.len() + out.as_bytes()[0] as usize) as i64;
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_chars_owned(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..150000 {
        let s = &values[i % 128];
        let cs: Vec<char> = s.chars().collect();
        black_box(&cs);
        sum += cs.len() as i64 + i64::from(u32::from(cs[2]));
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_trim_owned(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..200000 {
        let s = &values[i % 128];
        let out = s.trim_matches(|c: char| matches!(c as u32, 9..=13 | 32)).to_owned();
        black_box(&out);
        sum += (out.len() + out.as_bytes()[0] as usize) as i64;
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_repeat(seed: i64) -> (u128, i64) {
    let values = strings(seed);
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..200000 {
        let s = &values[i % 128];
        let out = s.repeat(i % 5 + 1);
        black_box(&out);
        sum += (out.len() + out.as_bytes()[0] as usize) as i64;
    }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_parse_int(seed: i64) -> (u128, i64) {
    let values: Vec<String> = (0..128).map(|i| (i * 777777 + seed).to_string()).collect();
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..300000 { sum += values[i % 128].parse::<i64>().unwrap(); }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_str_parse_float(seed: i64) -> (u128, i64) {
    let values: Vec<String> = (0..128).map(|i| format!("{}.125", i + seed)).collect();
    let mut sum = 0.0;
    let start = Instant::now();
    for i in 0..300000 { sum += values[i % 128].parse::<f64>().unwrap(); }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, (sum * 8.0) as i64)
}

fn bench_option_result(seed: i64) -> (u128, i64) {
    let options: Vec<_> = (0..500000).map(|i| if i % 3 == 0 { None } else { Some(i + seed) }).collect();
    let results: Vec<_> = (0..500000).map(|i| if i % 3 == 0 { Err(i + seed) } else { Ok(i + seed) }).collect();
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..500000 { sum += options[i].unwrap_or(1) + results[i].unwrap_or(2); }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_tuple_array_scan(seed: i64) -> (u128, i64) {
    let a: Vec<_> = (0..500000).map(|i| (seed + i, 3 * i)).collect();
    let mut sum = 0;
    let start = Instant::now();
    for &(x, y) in &a { sum += x + y; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_bool_logic_scan(seed: i64) -> (u128, i64) {
    let a: Vec<_> = (0..1000000).map(|i| (i + seed) % 7 < 3).collect();
    let mut sum = 0;
    let start = Instant::now();
    for &x in &a { if x { sum += 1; } }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_struct_array_scan(seed: i64) -> (u128, i64) {
    let a: Vec<_> = (0..500000).map(|i| Pair { x: seed + i, y: 3 * i }).collect();
    let mut sum = 0;
    let start = Instant::now();
    for pair in &a { sum += pair.x + pair.y; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn bench_array_clear_refill(seed: i64) -> (u128, i64) {
    let mut a = Vec::new();
    let mut sum = 0;
    let start = Instant::now();
    for i in 0..2000 { a.clear(); for j in 0..128 { a.push(seed + i + j); } sum += a[127]; }
    let elapsed = start.elapsed().as_nanos();
    (elapsed, sum)
}

fn main() {
    let mut name = String::new();
    let mut raw_seed = String::new();
    io::stdin().read_line(&mut name).unwrap();
    io::stdin().read_line(&mut raw_seed).unwrap();
    let seed = black_box(raw_seed.trim().parse().unwrap());
    let stats = match name.trim() {
        "int_arithmetic" => bench_int_arithmetic(seed),
        "float_arithmetic" => bench_float_arithmetic(seed),
        "array_fill" => bench_array_fill(seed),
        "array_push" => bench_array_push(seed),
        "array_pop" => bench_array_pop(seed),
        "array_scan" => bench_array_scan(seed),
        "array_index_read" => bench_array_index_read(seed),
        "array_index_write" => bench_array_index_write(seed),
        "array_front_insert_remove" => bench_array_front_insert_remove(seed),
        "array_reverse" => bench_array_reverse(seed),
        "array_sort" => bench_array_sort(seed),
        "array_contains" => bench_array_contains(seed),
        "array_owned_slice" => bench_array_owned_slice(seed),
        "array_extend" => bench_array_extend(seed),
        "array_snapshot_write" => bench_array_snapshot_write(seed),
        "str_concat" => bench_str_concat(seed),
        "str_owned_slice" => bench_str_owned_slice(seed),
        "str_contains" => bench_str_contains(seed),
        "str_prefix_suffix_eq" => bench_str_prefix_suffix_eq(seed),
        "str_split_owned" => bench_str_split_owned(seed),
        "str_join" => bench_str_join(seed),
        "str_chars_owned" => bench_str_chars_owned(seed),
        "str_trim_owned" => bench_str_trim_owned(seed),
        "str_repeat" => bench_str_repeat(seed),
        "str_parse_int" => bench_str_parse_int(seed),
        "str_parse_float" => bench_str_parse_float(seed),
        "option_result" => bench_option_result(seed),
        "tuple_array_scan" => bench_tuple_array_scan(seed),
        "bool_logic_scan" => bench_bool_logic_scan(seed),
        "struct_array_scan" => bench_struct_array_scan(seed),
        "array_clear_refill" => bench_array_clear_refill(seed),
        _ => panic!("unknown benchmark"),
    };
    println!("{} {}", stats.0, stats.1);
}
