#!/usr/bin/env bash

fast="false"

if [[ "$1" == "--fast" ]]; then
    shift
    fast="true"
fi

kserver="$HOME/k-framework/k-distribution/bin/kserver"

set -ex

pkill -f "kserver"

"$kserver" &> /dev/null &
kserver_pid=$!
if [[ "$fast" == "false" ]]; then
    # Warmup
    make exec &> /dev/null
fi
time make exec
kill "$kserver_pid"

"$kserver" &> /dev/null &
kserver_pid=$!
if [[ "$fast" == "false" ]]; then
    # Warmup
    make typecheck &> /dev/null
fi
time make typecheck
kill "$kserver_pid"

"$kserver" &> /dev/null &
kserver_pid=$!
if [[ "$fast" == "false" ]]; then
    # Warmup
    make compile &> /dev/null
fi
time make compile
kill "$kserver_pid"

