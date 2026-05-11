#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${1:-$SCRIPT_DIR/corpus}"

mkdir -p "$OUT_DIR"

write_file() {
    local path="$1"
    local tmp
    tmp="$(mktemp "${path}.tmp.XXXXXX")"
    cat >"$tmp"
    mv "$tmp" "$path"
}

generate_many_lets() {
    local path="$OUT_DIR/many_lets.hern"
    local count=1200
    {
        echo "#![no_implicit_prelude]"
        echo
        echo "let v0 = 0;"
        for i in $(seq 1 "$count"); do
            local prev=$((i - 1))
            echo "let v$i = v$prev;"
        done
        echo
        echo "v$count"
    } | write_file "$path"
}

generate_growing_env_polymorphic() {
    local path="$OUT_DIR/growing_env_polymorphic.hern"
    local count=360
    {
        echo "#![no_implicit_prelude]"
        echo
        for i in $(seq 0 "$count"); do
            echo "let id$i = fn(x) { x };"
            echo "let n$i = id$i($i);"
            echo "let s$i = id$i(\"value-$i\");"
        done
        echo
        echo "n$count"
    } | write_file "$path"
}

generate_many_functions() {
    local path="$OUT_DIR/many_functions.hern"
    local count=520
    {
        echo "#![no_implicit_prelude]"
        echo
        for i in $(seq 0 "$count"); do
            echo "fn pass$i(x) { x }"
            echo "let value$i = pass$i($i);"
        done
        echo
        echo "value$count"
    } | write_file "$path"
}

generate_large_records() {
    local path="$OUT_DIR/large_records.hern"
    local records=140
    local fields=90
    {
        echo "#![no_implicit_prelude]"
        echo
        echo "fn get_f042(row) { row.f042 }"
        for r in $(seq 0 "$records"); do
            echo "let record$r = #{"
            for f in $(seq -f "%03g" 0 "$fields"); do
                echo "  f$f: $((10#$f + r)),"
            done
            echo "};"
            echo "let picked$r = get_f042(record$r);"
        done
        echo
        echo "picked$records"
    } | write_file "$path"
}

generate_many_independent_errors() {
    local path="$OUT_DIR/many_independent_errors.hern"
    local count=420
    {
        echo "#![no_implicit_prelude]"
        echo
        for i in $(seq 0 "$count"); do
            echo "let bad$i: bool = $i;"
        done
    } | write_file "$path"
}

generate_many_lets
generate_growing_env_polymorphic
generate_many_functions
generate_large_records
generate_many_independent_errors

echo "Generated synthetic benchmark corpus in $OUT_DIR"
