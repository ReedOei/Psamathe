#!/usr/bin/env bash

if [[ -z "$1" ]] || [[ -z "$2" ]]; then
    echo "Usage: $0 ANALYZER CONTRACT_CSV [JOBS] [PER_JOB]"
    echo "ANALYZER - The Python script to use to analyze the files. This script should output to stdout."
    echo "CONTRACT_CSV - A csv file containing (filepath,solidity_version) pairs to analyze. For best results, do 'sort -t, -k2' on your csv file to make sure that all contracts with the same Solidity version are run in sequence, reducing the number of version changes necessary."
    echo "JOBS - The number of processes to run in parallel. Defaults to 1."
    echo "PER_JOB - How many files to give to each process. Defaults to 1."
    exit 1
fi

analyzer="$1"
contract_csv="$2"
job_num=1
per_job=1

if [[ -n "$3" ]]; then
    job_num="$3"
fi

if [[ -n "$4" ]]; then
    per_job="$4"
fi

running_jobs=0
to_run=()
old_ver="NONE"

cat "$contract_csv" | while read -r line; do
    fname="$(echo "$line" | cut -f1 -d,)"
    sol_ver="$(echo "$line" | cut -f2 -d,)"

    # echo "$line"

    if [[ "$old_ver" != "$sol_ver" ]]; then
        if [[ "${#to_run[@]}" -gt 0 ]]; then
            python3 "$analyzer" "${to_run[@]}" &
            to_run=()
        fi
        wait
        solc use "$sol_ver" > /dev/null
        old_ver="$sol_ver"
    fi

    to_run+=("$fname")

    if [[ "${#to_run[@]}" -ge "$per_job" ]]; then
        if [[ "$job_num" -eq "1" ]]; then
            python3 "$analyzer" "${to_run[@]}"
        else
            running_jobs="$(jobs -r | wc -l)"
            if [[ "$running_jobs" -ge "$job_num" ]]; then
                wait -n
            fi
            python3 "$analyzer" "${to_run[@]}" &
        fi

        to_run=()
    fi
done

