#!/usr/bin/env bash
scp -r src root@120.24.94.232:~/Website/
scp -r static root@120.24.94.232:~/Website/static
scp -r templates root@120.24.94.232:~/Website/templates
scp -r ../GoBase/src root@120.24.94.232:~/Website/
scp main.go root@120.24.94.232:~/Website/main.go
