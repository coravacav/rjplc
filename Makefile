TEST=test.jpl

.PHONY: compile

all: run

compile:
	cargo build --release --features homework

run:
	target/release/rjplc $(TEST)

clean:
	target
