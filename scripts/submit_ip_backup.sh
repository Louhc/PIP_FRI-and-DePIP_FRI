#!/bin/bash

wanIPs=()
while IFS= read -r line; do
  wanIPs+=("$line")
done < wan_ip.txt

# submit ips
for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    echo $i
    ssh -p 16789 weihan@$ip "mkdir -p /home/weihan/DeSNARK_R1CS/ips/" &
    scp -oStrictHostKeyChecking=accept-new -P 16789 lan_ip.txt weihan@$ip:/home/weihan/DeSNARK_R1CS/ips/ &
    scp -oStrictHostKeyChecking=accept-new -P 16789 ../snark/examples/snark_circom.rs weihan@$ip:/home/weihan/DeSNARK_R1CS/snark/examples/ &
    # scp -oStrictHostKeyChecking=accept-new -P 16789 ../snark/examples/snark_pre.rs weihan@$ip:/home/weihan/DeSNARK_R1CS/snark/examples/ &
done
wait

# change the parameters
for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    scp -oStrictHostKeyChecking=accept-new -P 16789 ../snark/data/32 weihan@$ip:/home/weihan/DeSNARK_R1CS/snark/data &
done
wait

# cargo build

PROCS=()
for i in "${!wanIPs[@]}"; do
    ip=${wanIPs[$i]}
    # ssh -p 16789 weihan@$ip "cd ~/DeSNARK_R1CS/snark/examples && ~/.cargo/bin/cargo clean" &
    ssh -p 16789 weihan@$ip "cd ~/DeSNARK_R1CS/snark/examples && RAYON_NUM_THREADS=32 RUSTFLAGS='-C target-cpu=native' ~/.cargo/bin/cargo build --release --example snark_circom" &
    pid=$!
    PROCS+=("$pid")
done
wait


## run the script
PROCS=()

for i in "${!wanIPs[@]}"; do
  ip=${wanIPs[$i]}

  echo $i
  
  ssh -p 16789 weihan@$ip "cd ~/DeSNARK_R1CS/snark/examples && RAYON_NUM_THREADS=32 ../../target/release/examples/snark_circom  $i ../data/32" 2>&1 | tee -a results/$ip.txt &
  
  pid=$!
  PROCS+=("$pid")
done
wait