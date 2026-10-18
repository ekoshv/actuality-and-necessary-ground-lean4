#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
printf 'UTC verification time: '
date -u '+%Y-%m-%dT%H:%M:%SZ'
printf '\nPinned toolchain:\n'
cat lean-toolchain
printf '\nCompiler:\n'
lake env lean --version
printf '\nDependency revision:\n'
git -C .lake/packages/mathlib rev-parse HEAD
printf '\nSource hashes:\n'
sha256sum ActualityGround.lean Audit.lean lakefile.toml lean-toolchain lake-manifest.json source/actuality_and_necessary_ground.pdf
printf '\nCOMMAND: lake env lean -DwarningAsError=true ActualityGround.lean\n'
lake env lean -DwarningAsError=true ActualityGround.lean
printf 'Source type-check exit code: 0\n'
printf '\nCOMMAND: lake build\n'
lake build
printf 'Build exit code: 0\n'
printf '\nCOMMAND: lake env lean -DwarningAsError=true Audit.lean\n'
lake env lean -DwarningAsError=true Audit.lean
printf 'Dependency audit exit code: 0\n'
printf '\nVERIFICATION PASSED\n'
