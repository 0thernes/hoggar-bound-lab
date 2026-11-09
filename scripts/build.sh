#!/usr/bin/env bash
# Builds the three native programs. Needs gcc only.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
QR=third_party/quantum_rng/src/quantum_rng
gcc -O2 -std=gnu11 -Wall -o build/hoggar src/hoggar.c $QR/quantum_rng.c -I$QR -lm 2>build/gcc-warnings.log
gcc -O2 -std=gnu11 -o build/qrng_stream src/qrng_stream.c $QR/quantum_rng.c -I$QR -lm 2>>build/gcc-warnings.log
gcc -O1 -std=gnu11 -Ithird_party/qgtl/include -Ithird_party/qgtl/stub \
    third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c src/qgt_hoggar.c \
    -o build/qgt_hoggar -lm 2>>build/gcc-warnings.log
echo "built: build/hoggar build/qrng_stream build/qgt_hoggar"
