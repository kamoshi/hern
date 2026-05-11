#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results"
BINARY="$ROOT/target/release/hern"

CORPUS=(
    "examples/astar.hern"
    "examples/factory_parse.hern"
    "examples/parser_test.hern"
)

WARMUP=3
RUNS=20

usage() {
    cat <<EOF
Usage: $0 <command> [name]

Commands:
  build              Build the release binary (cargo build --release)
  run                Run benchmarks, print results, no file saved
  save <name>        Run benchmarks and save results as a named baseline
  compare <name>     Run benchmarks and compare against a saved baseline

Examples:
  $0 save main          # establish baseline on main branch
  git checkout my-branch
  cargo build --release
  $0 compare main       # see if your branch is faster or slower
EOF
    exit 1
}

check_hyperfine() {
    if ! command -v hyperfine &>/dev/null; then
        echo "error: hyperfine not found — install with: brew install hyperfine"
        exit 1
    fi
}

build() {
    echo "==> cargo build --release"
    cargo build --release --manifest-path "$ROOT/Cargo.toml"
    echo "==> binary: $BINARY"
}

ensure_binary() {
    if [[ ! -f "$BINARY" ]]; then
        echo "Release binary not found; building first."
        build
    fi
}

slug_for() {
    local file="$1"
    local s="${file//\//_}"
    echo "${s%.hern}"
}

run_bench() {
    local file="$1"
    shift
    local path="$ROOT/$file"

    if [[ ! -f "$path" ]]; then
        echo "  warning: $file not found, skipping" >&2
        return
    fi

    hyperfine \
        --warmup "$WARMUP" \
        --runs   "$RUNS" \
        "$@" \
        "$BINARY typecheck $path"
}

cmd_run() {
    check_hyperfine
    ensure_binary
    for file in "${CORPUS[@]}"; do
        echo ""
        echo "--- $file ---"
        run_bench "$file"
    done
}

cmd_save() {
    local name="${1:-}"
    [[ -z "$name" ]] && { echo "error: save requires a name (e.g. 'main')"; usage; }

    check_hyperfine
    ensure_binary

    local dir="$RESULTS_DIR/$name"
    mkdir -p "$dir"
    cp "$BINARY" "$dir/hern"

    echo ""
    echo "Baseline '$name' saved to $dir/ (binary copied)"
}

cmd_compare() {
    local name="${1:-}"
    [[ -z "$name" ]] && { echo "error: compare requires a baseline name"; usage; }

    check_hyperfine
    ensure_binary

    local dir="$RESULTS_DIR/$name"
    if [[ ! -d "$dir" ]]; then
        echo "error: no baseline '$name' found at $dir"
        echo "Run '$0 save $name' first."
        exit 1
    fi

    local old="$dir/hern"
    if [[ ! -f "$old" ]]; then
        echo "error: no binary in baseline '$name' — re-run '$0 save $name'"
        exit 1
    fi

    for file in "${CORPUS[@]}"; do
        local path="$ROOT/$file"
        [[ -f "$path" ]] || { echo "warning: $file not found, skipping" >&2; continue; }
        echo ""
        echo "--- $file ---"
        hyperfine \
            --warmup "$WARMUP" \
            --runs   "$RUNS" \
            --command-name "$name"   "$old typecheck $path" \
            --command-name "current" "$BINARY typecheck $path"
    done
}

case "${1:-}" in
    build)   build ;;
    run)     cmd_run ;;
    save)    cmd_save "${2:-}" ;;
    compare) cmd_compare "${2:-}" ;;
    *)       usage ;;
esac
