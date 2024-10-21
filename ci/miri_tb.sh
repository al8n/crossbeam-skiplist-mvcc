#!/bin/bash
set -e

# Check if TARGET and CONFIG_FLAGS are provided, otherwise panic
if [ -z "$1" ]; then
  echo "Error: TARGET is not provided"
  exit 1
fi

TARGET=$1

rustup toolchain install nightly --component miri
rustup override set nightly
cargo miri setup

export MIRIFLAGS="-Zmiri-symbolic-alignment-check -Zmiri-disable-isolation -Zmiri-tree-borrows -Zmiri-ignore-leaks"

cargo miri test --tests --target $TARGET --lib

