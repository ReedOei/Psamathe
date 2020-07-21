#!/usr/bin/env bash

test_dir="$1"
shift

for fname in $(find "$test_dir" -name "*.flow" -type f); do
    "$(git rev-parse --show-toplevel)/flow" "$@" "$fname" | tee "$fname.out"
done

