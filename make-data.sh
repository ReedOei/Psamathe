#!/usr/bin/env bash

grep "," "$1" > "$1.csv"
grep -v "," "$1" | while read -r line; do
    IFS=';' read -ra ADDR <<< "$line"
    for i in "${ADDR[@]}"; do
        echo "$i"
    done
done > "$1-depth.csv"

