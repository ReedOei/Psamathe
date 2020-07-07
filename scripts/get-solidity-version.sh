#!/usr/bin/env bash

if [[ -z "$1" ]]; then
    echo "Usage: $0 DIR_PATH"
    echo "DIR_PATH - The directory containing the Solidity files to get the versions of."
    exit 1
fi

dir_path="$1"
ver_list="ver_list"

solc --versions > "$ver_list"

find "$dir_path" -name "*.sol" | while read -r fname; do
    sol_ver="$(grep -E "pragma solidity" "$fname" | head -n+1 | sed -E "s/^pragma solidity *(\^)?([0-9\.]*)[^0-9\.].*/\2/g")"
    if [[ -z "$sol_ver" ]]; then
        continue
    elif grep -q "^$sol_ver$" "$ver_list"; then
        echo "$fname,$sol_ver"
    elif [[ "$sol_ver" =~ 0.4 ]]; then
        echo "$fname,0.4.26"
    fi
done

