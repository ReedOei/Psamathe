#!/usr/bin/env bash

input_file="$1"
output_file="$(dirname "$input_file")/$(basename "$input_file" ".flow").sol"
temp="$(mktemp XXXXXXXXX.sol)"

# Invoke the pure-flow-compiler
"$(dirname "$0")"/flow pure-compile --pattern "<k> Code </k>" "$1" \
    | tail -n+4 \
    | head -n-1 \
    | sed -E "s/(\.SolVarDefs|\.SolStmts|\.SolDecls|, \.Exprs|, \.SolArgs)| ~> \.//g" \
    | sed -E "s/ \.SolArgs//g" \
    |& tee "$output_file"

# Clean up generated code
npx prettier "$output_file" | tee "$temp"
mv "$temp" "$output_file"

# Try to compile it
solc "$output_file"

