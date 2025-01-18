TEST=test.jpl

all: run

compile:
	cargo build --release

run:
	target/release/template $(TEST) -l

clean:
	target
