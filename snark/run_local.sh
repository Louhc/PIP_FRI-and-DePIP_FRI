 #!/usr/bin/bash

set -ex
trap "exit" INT TERM
trap "kill 0" EXIT

cargo build --release --example $1 --no-default-features --features "parallel"
# RUSTFLAGS="-C target-feature=+bmi2,+adx" cargo +nightly build --release --example $1 --no-default-features --features "parallel asm"
BIN=../target/release/examples/$1

PROCS=()
for i in 0 1 2 3
do
  RAYON_NUM_THREADS=4 $BIN $i ./data/4_local &
  #RUST_LOG=debug $BIN $i ./data/4 &
  pid=$!
  PROCS+=("$pid")
done
jobs -pr

for pid in $PROCS
do
  jobs -pr
  wait $pid
  jobs -pr
done

echo done
