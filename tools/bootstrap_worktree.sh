#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$HOME/.local/bin:/usr/local/bin:/opt/homebrew/bin:$PATH"
MAIN_REPO="/Users/pablosuarez/Desktop/S4TuringPoisson"
if [ "$(pwd -P)" = "$(cd "$MAIN_REPO" && pwd -P)" ]; then
  echo "[bootstrap_worktree] In main repo; .lake/packages ready."
  exit 0
fi
mkdir -p .lake
if [ ! -d ".lake/packages/TauCeti" ]; then
  echo "[bootstrap_worktree] Cloning .lake/packages via APFS CoW from $MAIN_REPO ..."
  rm -rf .lake/packages
  cp -Rc "$MAIN_REPO/.lake/packages" .lake/packages
  echo "[bootstrap_worktree] Done."
else
  echo "[bootstrap_worktree] .lake/packages/TauCeti already present."
fi
