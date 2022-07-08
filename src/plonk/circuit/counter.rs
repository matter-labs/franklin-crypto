use std::sync::atomic::{AtomicUsize, Ordering};

pub static SOME_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn reset_counter() {
    SOME_COUNTER.store(0, Ordering::Relaxed);
}

pub fn increment_counter() {
    SOME_COUNTER.fetch_add(1, Ordering::SeqCst);
}

pub fn increment_counter_by(val: usize) {
    SOME_COUNTER.fetch_add(val, Ordering::SeqCst);
}

pub fn output_counter() -> usize {
    SOME_COUNTER.load(Ordering::Relaxed)
}
