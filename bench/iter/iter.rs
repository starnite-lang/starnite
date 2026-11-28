// The same sums in Rust, two ways: iterators whose types the compiler sees through (static),
// and iterators behind Box<dyn Iterator>, one call through a pointer per value and stage, which
// is what an Iter[T] is.
use std::io::Read;
fn count_dyn(from: i64, to: i64) -> Box<dyn Iterator<Item = i64>> { Box::new(from..to) }
fn filter_dyn(it: Box<dyn Iterator<Item = i64>>, f: Box<dyn Fn(i64) -> bool>) -> Box<dyn Iterator<Item = i64>> { Box::new(it.filter(move |x| f(*x))) }
fn map_dyn(it: Box<dyn Iterator<Item = i64>>, f: Box<dyn Fn(i64) -> i64>) -> Box<dyn Iterator<Item = i64>> { Box::new(it.map(move |x| f(x))) }
fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let which = s.trim();
    let mut sum: i64 = 0;
    for r in 0..20i64 {
        let r = std::hint::black_box(r);
        match which {
            "iter-static" => for x in 0..10000000i64 { sum = sum.checked_add(x + r).unwrap(); },
            "iter-dyn" => for x in count_dyn(0, 10000000) { sum = sum.checked_add(x + r).unwrap(); },
            "iter3-static" => for x in (0..10000000i64).filter(|x| x % 3 == 0).map(|x| x * 2) { sum = sum.checked_add(x + r).unwrap(); },
            "iter3-dyn" => for x in map_dyn(filter_dyn(count_dyn(0, 10000000), Box::new(|x| x % 3 == 0)), Box::new(|x| x * 2)) { sum = sum.checked_add(x + r).unwrap(); },
            _ => panic!("unknown case"),
        }
    }
    println!("{}", sum);
}
