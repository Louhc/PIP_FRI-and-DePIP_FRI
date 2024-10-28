 #!/usr/bin/bash

set -ex
trap "exit" INT TERM
trap "kill 0" EXIT

# cargo build --example $1 --release
cargo build --release --example $1 --no-default-features --features "parallel"
BIN=../target/release/examples/$1

PROCS=()
for i in 0 1 
do
  RAYON_NUM_THREADS=8 $BIN $i ./data/2_local &
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
