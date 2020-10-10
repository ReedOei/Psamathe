#!/usr/bin/env bash

test_dir="$1"
shift

for fname in $(find "$test_dir" -name "*.flow" -type f); do
    FLAGS=()
    if [[ -e "$fname.pat" ]]; then
        FLAGS+=("--pattern")
        FLAGS+=("$(cat "$fname.pat")")
    fi
    "$(git rev-parse --show-toplevel)/flow" "$@" "${FLAGS[@]}" "$fname" | tee "$fname.out"
done

