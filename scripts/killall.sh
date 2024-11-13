
#!/usr/bin/env bash

wanIPs=()
while IFS= read -r line; do
  wanIPs+=("$line")
done < wan_ip.txt

for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    ssh -p 16789 weihan@$ip killall snark_pre &
done
wait

