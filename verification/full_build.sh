#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="/root/.elan/bin:$PATH"
export LEAN_NUM_THREADS=2
mkdir -p verification/scratch
for scratch in ExactZCDP/*Scratch.lean; do
  if [[ -f "$scratch" ]]; then mv "$scratch" verification/scratch/; fi
done
if [[ -d .lake/build ]]; then
  mv .lake/build "verification/preclean-build-$(date -u +%Y%m%dT%H%M%SZ)"
fi
date -u +%FT%TZ
lean --version
lake --version
uname -sm
# Topological builds bound simultaneous compiler memory while retaining normal Lake traces.
for module in Base Calculus Mechanism Parameters ShapeBounds Shape RootEquation EndpointLimit BisectionValue Bisection Main Certificates; do
  taskset -c 0-2 lake --wfail build "+ExactZCDP.$module"
done
taskset -c 0-2 lake --wfail build
taskset -c 0-2 lake env lean -j1 verification/Audit.lean > verification/axioms.log 2>&1
date -u +%FT%TZ
printf '%s\n' 'FULL_PROJECT_BUILD_AND_AXIOM_AUDIT_PASS'
