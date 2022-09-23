#![no_main]

use arena_btree::differential::*;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: (Vec<(Key, Value)>, Vec<MapOperation>)| {
    let (initial_map, operations) = data;
    if let Err(e) = differential_test_map(initial_map, operations) {
        eprintln!("====================================================================");
        eprintln!("{e}");
        eprintln!("====================================================================");
        panic!("{e}");
    }
});
