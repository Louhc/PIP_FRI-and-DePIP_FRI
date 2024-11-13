#!/usr/bin/env bash

num=${1:-8}
head -n $num < lan_ip.txt > lan_ip_$num.txt
head -n $num < wan_ip.txt > wan_ip_$num.txt

readarray -t wanIPs < wan_ip_$num.txt 
    
for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    ssh -p 16789 weihan@$ip "RUST_BACKTRACE=1 /home/weihan/DeSNARK_R1CS/target/release/examples/snark_pre $i /home/weihan/ip.txt" 2>&1 | tee -a $ip.txt &
done
wait