default:
  just --list

measure-t-l:
    cargo run -rq -F measure -- -ql --measure-repeat t.jpl
measure-t-l-long:
    cargo run -rq -F measure -- -ql --measure-repeat --measure-repeat t.jpl

measure-t-p:
    cargo run -rq -F measure -- -qp --measure-repeat t.jpl
measure-t-p-long:
    cargo run -rq -F measure -- -qp --measure-repeat --measure-repeat t.jpl

bench-t-l:
    just cr
    hyperfine 'target/release/rjplc -l t.jpl > /dev/null' --warmup 25
    
bench-t-p:
    just cr
    hyperfine 'target/release/rjplc -p t.jpl > /dev/null' --warmup 25
    
bench-t-t:
    just cr
    hyperfine 'target/release/rjplc -t t.jpl > /dev/null' --warmup 25

bench-t-l-q:
    just cr
    hyperfine 'target/release/rjplc -lq t.jpl' --warmup 25
    
bench-t-p-q:
    just cr
    hyperfine 'target/release/rjplc -pq t.jpl' --warmup 25

bench-t-t-q:
    just cr
    hyperfine 'target/release/rjplc -tq t.jpl' --warmup 25

cr: cargo-build-release
cargo-build-release:
    cargo build --release

build-debug:
    CARGO_PROFILE_RELEASE_DEBUG=true cargo build --release
    codesign -s "Stefan Todorov" -f --timestamp --options=runtime --entitlements ent.plist target/release/rjplc
