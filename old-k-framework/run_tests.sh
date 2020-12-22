#!/usr/bin/env bash

fast="false"

if [[ "$1" == "--fast" ]]; then
    shift
    fast="true"
fi

run_target() {
    target="$1"

    "$kserver" &> /dev/null &
    kserver_pid=$!
    if [[ "$fast" == "false" ]]; then
        echo "[INFO] Warming up: $target"
        make "$target"
        echo "[INFO] Done warming up: $target"
    fi
    time make "$target"
    kill "$kserver_pid"
}

kserver="$HOME/k-framework/k-distribution/bin/kserver"

pkill -f "kserver"

set -ex

run_target "exec"
run_target "typecheck"
run_target "compile"
run_target "pure-flow"

