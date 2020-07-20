#!/usr/bin/env bash

test_dir="$1"
shift
rerun_all="$1"
shift

for fname in $(find "$test_dir" -name "*.flow" -type f); do
    if [[ -e "$fname.out" ]] && [[ -z "$rerun_all" ]]; then
        echo "[INFO] Skipping $fname, output file already exists."
        continue
    fi

    "$(git rev-parse --show-toplevel)/flow" "$@" "$fname" > "$fname.out"
done

