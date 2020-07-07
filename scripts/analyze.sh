#!/usr/bin/env bash

if [[ -z "$1" ]] || [[ -z "$2" ]]; then
    echo "Usage: $0 ANALYZER CONTRACT_CSV [JOBS]"
    echo "ANALYZER - The Python script to use to analyze the files. This script should output some number lines of a CSV file for each input file to stdout."
    echo "CONTRACT_CSV - A csv file containing (filepath,solidity_version) pairs to analyze. For best results, do 'sort -t, -k2' on your csv file to make sure that all contracts with the same Solidity version are run in sequence, reducing the number of version changes necessary."
    echo "JOBS - Currently does not work! (The number of processes to run in parallel.)"
    exit 1
fi

analyzer="$1"
contract_csv="$2"
job_num=1
running_jobs=0

if [[ -n "$3" ]]; then
    job_num="$3"
fi

old_ver="NONE"

cat "$contract_csv" | while read -r line; do
    fname="$(echo "$line" | cut -f1 -d,)"
    sol_ver="$(echo "$line" | cut -f2 -d,)"

    if [[ "$old_ver" != "$sol_ver" ]]; then
        wait
        solc use "$sol_ver" > /dev/null
        old_ver="$sol_ver"
    fi

    running_jobs="$(jobs -r | wc -l)"
    if [[ "$running_jobs" -ge "$job_num" ]]; then
        wait -n
    fi
    python3 "$analyzer" "$fname" &
    running_jobs="$(jobs -r | wc -l)"
done

