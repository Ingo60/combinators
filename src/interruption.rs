#![allow(non_upper_case_globals)]

use ctrlc::set_handler;
use std::sync::atomic;

static sigint_received: atomic::AtomicBool = atomic::AtomicBool::new(false);

pub fn reset() {
    sigint_received.store(false, atomic::Ordering::SeqCst);
}

pub fn was_interrupted() -> bool {
    sigint_received.load(atomic::Ordering::SeqCst)
}

pub fn initialize() {
    set_handler(|| sigint_received.store(true, atomic::Ordering::SeqCst))
        .expect("setting Ctrl-C handler");
}
