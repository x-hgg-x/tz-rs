#!/bin/sh

set -e

fmt_cmd="cargo fmt --all -- --check"
echo "+ $fmt_cmd"
$fmt_cmd

run() {
    cargo_arg=$1
    bin_arg=$2

    for rust in "1.81" "stable" "nightly"; do
        for const in "" "const"; do
            for feature in "" "alloc" "std"; do
                cmd="cargo +$rust -q $cargo_arg --no-default-features --features=$const,$feature $bin_arg"
                echo "+ $cmd"
                $cmd
                echo "\n"
            done
        done
    done
}

run "clippy" "-- -D warnings"
run "test"
