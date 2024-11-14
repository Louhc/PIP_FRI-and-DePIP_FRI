
#!/usr/bin/env bash

wanIPs=()
while IFS= read -r line; do
  wanIPs+=("$line")
done < wan_ip.txt

for i in ${!wanIPs[@]}; do
    ip=${wanIPs[$i]}
    ssh root@$ip killall snark_circom &
done
wait

