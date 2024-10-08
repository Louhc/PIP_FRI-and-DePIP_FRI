 #!/usr/bin/bash

set -ex
trap "exit" INT TERM
trap "kill 0" EXIT

cargo build --example $1 --release
BIN=../target/release/examples/$1

PROCS=()
for i in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
do
  $BIN $i ./data/16 &
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
