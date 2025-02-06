use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    str::FromStr,
    time::Instant,
};

thread_local! {
    pub static SUM_TIMINGS_MAP: RefCell<HashMap<&'static str, u128>> = RefCell::new(HashMap::new());
    pub static CURRENT_TIMINGS_STACK: RefCell<Vec<&'static str>> = const { RefCell::new(vec![]) };
    pub static TREE_TIMINGS: RefCell<HashMap<u8, HashMap<String, u128>>> = RefCell::new(HashMap::new());
    static MEASURE_ITERATIONS: Cell<u128> = const { Cell::new(1) };
}

pub struct MeasureHandle {
    pub name: &'static str,
    pub start: Instant,
}

impl Drop for MeasureHandle {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed().as_nanos();

        SUM_TIMINGS_MAP.with(|timings_map| {
            *timings_map.borrow_mut().entry(self.name).or_insert(0) += elapsed;
        });

        CURRENT_TIMINGS_STACK.with(|stack| {
            TREE_TIMINGS.with(|timings_map| {
                let mut stack_str = String::from_str(stack.borrow().first().unwrap()).unwrap();
                let mut previous_layer = "";
                let mut level = 1;
                for layer in stack.borrow().iter().skip(1) {
                    if *layer == previous_layer {
                        continue;
                    }
                    previous_layer = layer;
                    stack_str.push_str("->");
                    stack_str.push_str(layer);
                    level += 1;
                }

                *timings_map
                    .borrow_mut()
                    .entry(level)
                    .or_default()
                    .entry(stack_str)
                    .or_insert(0) += elapsed;
            });

            stack.borrow_mut().pop();
        });
    }
}

pub fn set_measure_iterations(iterations: u128) {
    MEASURE_ITERATIONS.with(|i| i.set(iterations));
}

#[macro_export]
macro_rules! measure {
    ($name:expr) => {
        #[cfg(feature = "measure")]
        let _measure = $crate::measure::MeasureHandle {
            name: $name,
            start: std::time::Instant::now(),
        };
        #[cfg(feature = "measure")]
        $crate::measure::CURRENT_TIMINGS_STACK.with(|stack| {
            stack.borrow_mut().push($name);
        });
    };
}

#[allow(clippy::too_many_lines)]
pub fn print_timings() {
    #[cfg(feature = "measure")]
    {
        use colored::Colorize;
        use itertools::Itertools;

        if let reps @ 2.. = MEASURE_ITERATIONS.with(|i| i.get()) {
            println!("Repeated measurements {} times", reps);
        }

        TREE_TIMINGS.with(|timings_map| {
            fn get_children(
                map: &HashMap<u8, HashMap<String, u128>>,
                level: u8,
                name: &str,
            ) -> Vec<(String, u128)> {
                let Some(pos) = map.get(&(level + 1)) else {
                    return vec![];
                };

                let mut children = pos
                    .iter()
                    .filter(|(n, _)| n.starts_with(name))
                    .map(|(n, e)| (n.to_string(), *e))
                    .collect_vec();

                children.sort_by(|a, b| b.1.cmp(&a.1));

                children
            }

            fn recur_write_tree(
                map: &HashMap<u8, HashMap<String, u128>>,
                children: &[(String, u128)],
                col_widths: &[(usize, usize)],
                level: u8,
            ) {
                for (name, elapsed) in children {
                    let printed_name = name.split("->").last().unwrap();
                    let children = get_children(map, level + 1, name);

                    let time = if children.is_empty() {
                        dur::Duration::from_nanos(*elapsed / MEASURE_ITERATIONS.with(|i| i.get()))
                            .to_string()
                    } else {
                        format!(
                            "{} {}",
                            dur::Duration::from_nanos(
                                *elapsed
                                    - children.iter().map(|(_, e)| *e).sum::<u128>()
                                        / MEASURE_ITERATIONS.with(|i| i.get()),
                            ),
                            dur::Duration::from_nanos(
                                *elapsed / MEASURE_ITERATIONS.with(|i| i.get())
                            )
                            .to_string()
                            .dimmed()
                        )
                    };

                    let printed_name = if printed_name == *name {
                        format!("{} {}", name.blue(), time)
                    } else {
                        let printed_name = format!("-> {printed_name}").blue();
                        let printed_name = format!("{printed_name} {time}");
                        let (total_width, _) = col_widths.get(level as usize).unwrap();
                        format!(
                            "{printed_name:>total_width$}",
                            total_width = total_width + printed_name.len(),
                        )
                    };

                    println!("{printed_name}");
                    recur_write_tree(map, &children, col_widths, level + 1);
                }
            }

            let timings_map = timings_map.borrow();

            let widths = timings_map
                .values()
                .flat_map(|v| v.keys())
                .map(|s| s.split("->").map(str::len).collect_vec())
                .collect_vec();

            let mut max_col_widths: Vec<usize> = vec![];

            for pieces in widths {
                if pieces.len() > max_col_widths.len() {
                    max_col_widths.resize(pieces.len(), 0);
                }

                for (i, &w) in pieces.iter().enumerate() {
                    max_col_widths[i] = max_col_widths[i].max(w);
                }
            }

            let mut col_widths = vec![];
            for (i, w) in max_col_widths.into_iter().enumerate() {
                col_widths.push((
                    col_widths
                        .get(i.saturating_sub(1))
                        .copied()
                        .map_or(0, |(t, ow)| t + ow),
                    if i > 0 { w + 3 } else { w },
                ));
            }

            recur_write_tree(
                &timings_map,
                &get_children(&timings_map, 0, ""),
                &col_widths,
                1,
            );
        });

        SUM_TIMINGS_MAP.with(|timings_map| {
            let timings_map = timings_map.borrow();
            let mut timings_map = timings_map.iter().collect_vec();
            timings_map.sort_by(|a, b| b.1.cmp(&a.1));
            for (name, elapsed) in timings_map {
                println!(
                    "{name} {}",
                    dur::Duration::from_nanos(*elapsed / MEASURE_ITERATIONS.with(|i| i.get()))
                );
            }
        });
    }
}
