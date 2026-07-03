setip=$(ipconfig getifaddr en0)
sudo networksetup -setmanual "Wi-Fi" $setip 255.255.255.0 192.168.31.88
sudo networksetup -setdnsservers "Wi-Fi" 192.168.31.88