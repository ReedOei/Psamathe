#!/usr/bin/env bash

# output_file="compiled.sol"
output_file="$(mktemp XXXXXXXXX.sol)"
./flow pure-compile --pattern "<k> Code </k>" "$1" \
    | tail -n+4 \
    | head -n-1 \
    | sed -E "s/(\.SolVarDefs|\.SolStmts|\.SolDecls|, \.Exprs|, \.SolArgs)| ~> \.//g" \
    | sed -E "s/ \.SolArgs//g" \
    |& tee "$output_file"
npx prettier "$output_file"

