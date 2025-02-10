TEST=test.jpl
FLAGS=

.PHONY: compile

all: run

compile:
	cargo build --release --features homework

run:
	target/release/rjplc $(FLAGS) $(TEST) 

clean:
	target
