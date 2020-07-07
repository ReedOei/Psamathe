#!/usr/bin/env bash

old_ver="NONE"
contract_csv="$1"
mkdir -p "results"

cat "$contract_csv" | while read -r line; do
    fname="$(echo "$line" | cut -f1 -d,)"
    sol_ver="$(echo "$line" | cut -f2 -d,)"
    res_path="results/$(basename "$fname")"

    if [[ -f "$res_path" ]]; then
        echo "[INFO] Skipping $fname, already analyzed."
        continue
    fi

    echo "[INFO] Checking $fname, putting results in $res_path"

    if [[ "$old_ver" != "$sol_ver" ]]; then
        solc use "$sol_ver"
        old_ver="$sol_ver"
    fi

    python3 structures.py "$fname" > "$res_path"
done

