TEST=test.jpl

.PHONY: compile

all: run

compile:
	cargo build --release

run:
	target/release/template $(TEST)

clean:
	target
