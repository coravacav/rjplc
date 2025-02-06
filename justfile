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

bench-t-p:
    just cr
    hyperfine 'target/release/rjplc -p t.jpl > /dev/null' --warmup 25

cr: cargo-build-release
cargo-build-release:
    cargo build --release

crd: cargo-build-release-debug
cargo-build-release-debug:
    CARGO_PROFILE_RELEASE_DEBUG=true just cargo-build-release
