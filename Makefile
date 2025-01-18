TEST=test.jpl

all: run

compile:
	cargo build

run:
	cargo run -q -- $(TEST) -l

clean:
	target
