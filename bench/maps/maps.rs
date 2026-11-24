// SPDX-License-Identifier: GPL-3.0-or-later
// The Rust control for bench/maps: the standard HashMap and HashSet, whose default hasher is
// SipHash-1-3 under a random key, as Starnite's is. Built with overflow checks on.
use std::collections::{HashMap, HashSet};
use std::hint::black_box;
use std::io;
use std::time::Instant;

#[derive(PartialEq, Eq, Hash)]
struct Point { x: i64, y: i64 }

fn key(i: i64, seed: i64) -> i64 { (i * 7919 + seed) % 1000003 }

fn filled_map(n: i64, seed: i64) -> HashMap<i64, i64> {
    let mut m = HashMap::new();
    for i in 0..n { m.insert(key(i, seed), i); }
    m
}

fn names(seed: i64) -> Vec<String> {
    (0..512).map(|i| format!("name{}/item", (i * 37 + seed) % 100000)).collect()
}

fn run(name: &str, seed: i64) -> (u128, i64) {
    match name {
        "map_insert_int" => {
            let start = Instant::now();
            let m = filled_map(200000, seed);
            let elapsed = start.elapsed().as_nanos();
            (elapsed, m.len() as i64 + m[&key(7, seed)] + m[&key(199999, seed)])
        }
        "map_lookup_int" => {
            let m = filled_map(100000, seed);
            let mut sum = 0i64;
            let start = Instant::now();
            for i in 0..1000000i64 {
                match m.get(&key(i % 200000, seed)) { Some(v) => sum += *v, None => sum += 1 }
            }
            (start.elapsed().as_nanos(), sum)
        }
        "map_update_int" => {
            let mut m: HashMap<i64, i64> = HashMap::new();
            let start = Instant::now();
            for i in 0..1000000i64 { *m.entry((i * 31 + seed) % 50021).or_insert(0) += 1; }
            let elapsed = start.elapsed().as_nanos();
            (elapsed, m.len() as i64 * 1000 + m[&(seed % 50021)])
        }
        "map_iter_int" => {
            let m = filled_map(200000, seed);
            let mut sum = 0i64;
            let start = Instant::now();
            for _ in 0..5 { for (k, v) in &m { sum += *k - *v; } }
            (start.elapsed().as_nanos(), sum)
        }
        "map_remove_int" => {
            let mut m = filled_map(200000, seed);
            let mut found = 0i64;
            let start = Instant::now();
            for i in 0..200000i64 {
                if i % 2 == 0 { if let Some(v) = m.remove(&key(i, seed)) { found += v; } }
            }
            let elapsed = start.elapsed().as_nanos();
            (elapsed, m.len() as i64 + found)
        }
        "map_count_str" => {
            let keys = names(seed);
            let mut m: HashMap<String, i64> = HashMap::new();
            let start = Instant::now();
            for i in 0..300000usize {
                let k = &keys[(i * 7) % 512];
                match m.get_mut(k) { Some(v) => *v += 1, None => { m.insert(k.clone(), 1); } }
            }
            let elapsed = start.elapsed().as_nanos();
            (elapsed, m.len() as i64 * 1000000 + m[&keys[3]])
        }
        "set_int" => {
            let mut s: HashSet<i64> = HashSet::new();
            let mut hits = 0i64;
            let start = Instant::now();
            for i in 0..200000i64 { s.insert(key(i, seed)); }
            for i in 0..1000000i64 { if s.contains(&key(i % 400000, seed)) { hits += 1; } }
            let elapsed = start.elapsed().as_nanos();
            (elapsed, s.len() as i64 + hits)
        }
        "set_union" => {
            let mut a: HashSet<i64> = HashSet::new();
            let mut b: HashSet<i64> = HashSet::new();
            for i in 0..100000i64 { a.insert(key(i, seed)); b.insert(key(i + 50000, seed)); }
            let start = Instant::now();
            let u: HashSet<i64> = a.union(&b).copied().collect();
            let n: HashSet<i64> = a.intersection(&b).copied().collect();
            let d: HashSet<i64> = a.difference(&b).copied().collect();
            let elapsed = start.elapsed().as_nanos();
            (elapsed, u.len() as i64 * 3 + n.len() as i64 * 5 + d.len() as i64 * 7)
        }
        "map_struct_key" => {
            let mut m: HashMap<Point, i64> = HashMap::new();
            let mut sum = 0i64;
            let start = Instant::now();
            for i in 0..100000i64 { m.insert(Point { x: key(i, seed), y: i % 7 }, i); }
            for i in 0..500000i64 {
                match m.get(&Point { x: key(i % 200000, seed), y: i % 200000 % 7 }) { Some(v) => sum += *v, None => sum += 1 }
            }
            (start.elapsed().as_nanos(), m.len() as i64 + sum)
        }
        "map_tuple_key" => {
            let mut m: HashMap<(i64, i64), i64> = HashMap::new();
            let mut sum = 0i64;
            let start = Instant::now();
            for i in 0..100000i64 { m.insert((key(i, seed), i % 7), i); }
            for i in 0..500000i64 {
                match m.get(&(key(i % 200000, seed), i % 200000 % 7)) { Some(v) => sum += *v, None => sum += 1 }
            }
            (start.elapsed().as_nanos(), m.len() as i64 + sum)
        }
        "map_str_values" => {
            // the values are shared strings, as Starnite's are: a clone is a count, not a copy
            let words: Vec<std::rc::Rc<str>> = names(seed).into_iter().map(|w| std::rc::Rc::from(w.as_str())).collect();
            let mut m: HashMap<i64, std::rc::Rc<str>> = HashMap::new();
            let mut sum = 0i64;
            let start = Instant::now();
            for i in 0..200000i64 { m.insert(key(i % 50000, seed), words[(i % 512) as usize].clone()); }
            for i in 0..500000i64 {
                match m.get(&key(i % 100000, seed)) { Some(w) => sum += w.len() as i64, None => sum += 1 }
            }
            (start.elapsed().as_nanos(), m.len() as i64 + sum)
        }
        _ => panic!("unknown benchmark"),
    }
}

fn main() {
    let mut name = String::new();
    let mut raw_seed = String::new();
    io::stdin().read_line(&mut name).unwrap();
    io::stdin().read_line(&mut raw_seed).unwrap();
    let seed: i64 = black_box(raw_seed.trim().parse().unwrap());
    let (elapsed, checksum) = run(name.trim(), seed);
    println!("{} {}", elapsed, checksum);
}
