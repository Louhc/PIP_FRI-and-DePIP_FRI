#!/bin/bash

wanIPs=()
while IFS= read -r line; do
  wanIPs+=("$line")
done < wan_ip.txt

# submit ips
for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    echo $i
    # ssh -oStrictHostKeyChecking=no root@$ip "cd ~/DeSNARK_R1CS/snark/data && unxz circuit.r1cs.xz && tar -xJvf witness.tar.xz" &
    # ssh -oStrictHostKeyChecking=no root@$ip "rm -rf /home/weihan/DeSNARK_R1CS/" &
    # ssh -oStrictHostKeyChecking=no root@$ip "git clone git@github.com:leeweihanwickham/DeSNARK_R1CS.git" &
    # ssh -oStrictHostKeyChecking=no root@$ip "mkdir -p DeSNARK_R1CS/ips/" &
    # scp -oStrictHostKeyChecking=accept-new lan_ip.txt root@$ip:DeSNARK_R1CS/ips/ &
    scp -oStrictHostKeyChecking=accept-new ../snark/examples/snark_circom.rs root@$ip:DeSNARK_R1CS/snark/examples/ &
done
wait

# change the parameters
for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    scp -oStrictHostKeyChecking=accept-new ../snark/data/8 root@$ip:DeSNARK_R1CS/snark/data &
done
wait

# # cargo build

PROCS=()
for i in "${!wanIPs[@]}"; do
    ip=${wanIPs[$i]}
    # ssh -p 16789 weihan@$ip "cd ~/DeSNARK_R1CS/snark/examples && ~/.cargo/bin/cargo clean" &
    ssh root@$ip "cd ~/DeSNARK_R1CS/snark && RAYON_NUM_THREADS=32 RUSTFLAGS='-C target-cpu=native -C target-feature=+bmi2,+adx' cargo build --release --example snark_circom" &
    pid=$!
    PROCS+=("$pid")
done
wait


# ## run the script

PROCS=()
for i in "${!wanIPs[@]}"; do
  ip=${wanIPs[$i]}
  echo $i
  ssh root@$ip "cd ~/DeSNARK_R1CS/snark && RAYON_NUM_THREADS=32 ../target/release/examples/snark_circom  $i ./data/8" 2>&1 | tee -a results/$ip.txt &
  pid=$!
  PROCS+=("$pid")
done
wait