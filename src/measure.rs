use std::{cell::RefCell, collections::HashMap, time::Instant};

thread_local! {
    static TIMINGS_MAP: RefCell<HashMap<&'static str, u128>> = RefCell::new(HashMap::new());
}

pub struct MeasureHandle {
    pub name: &'static str,
    pub start: Instant,
}

impl Drop for MeasureHandle {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed().as_nanos();
        // println!("{} {}", self.name, elapsed);

        TIMINGS_MAP.with(|timings_map| {
            *timings_map.borrow_mut().entry(self.name).or_insert(0) += elapsed;
        });
    }
}

#[macro_export]
macro_rules! measure {
    ($name:expr) => {
        #[cfg(feature = "measure")]
        let _measure = $crate::measure::MeasureHandle {
            name: $name,
            start: std::time::Instant::now(),
        };
    };
}

pub fn print_timings() {
    #[cfg(feature = "measure")]
    TIMINGS_MAP.with(|timings_map| {
        use itertools::Itertools;

        for (name, elapsed) in timings_map.borrow().iter().sorted_by(|a, b| a.1.cmp(b.1)) {
            use colored::Colorize;
            println!("{}: {}", name.blue(), dur::Duration::from_nanos(*elapsed));
        }
    });
}
