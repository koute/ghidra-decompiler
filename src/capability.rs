use std::sync::atomic::{AtomicBool, Ordering};

use crate::error::Result;

pub trait CapabilityPoint: Sync {
    fn initialize(&self) -> Result<()>;
}

static CAPABILITY_POINTS: &[&dyn CapabilityPoint] = &[];

static LIST_CLEARED: AtomicBool = AtomicBool::new(false);

pub fn get_list() -> &'static [&'static dyn CapabilityPoint] {
    if LIST_CLEARED.load(Ordering::SeqCst) {
        return &[];
    }
    CAPABILITY_POINTS
}

pub fn initialize_all() -> Result<()> {
    let list = get_list();
    for ptr in list.iter() {
        ptr.initialize()?;
    }
    LIST_CLEARED.store(true, Ordering::SeqCst);
    Ok(())
}
