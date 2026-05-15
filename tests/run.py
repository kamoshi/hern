#!/usr/bin/env python3
import argparse
import os
import subprocess
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor, as_completed

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEST_TOML_PATH = os.path.join(REPO_ROOT, "tests", "test.toml")
DEFAULT_LUA = os.environ.get("HERN_TEST_LUA", "luajit")

ALLOWED_EXPECTS = {"typecheck", "error", "test"}
ALLOWED_KEYS = {
    "path",
    "expect",
    "output",
    "error_contains",
    "tags",
    "purpose",
    "fixtures",
}


def parse_args():
    parser = argparse.ArgumentParser(description="Run Hern black-box tests.")
    parser.add_argument(
        "patterns",
        nargs="*",
        help="Run tests whose name contains any of these patterns.",
    )
    parser.add_argument(
        "--tag",
        action="append",
        default=[],
        help="Run tests with this tag. May be passed more than once.",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List selected tests without building or running them.",
    )
    parser.add_argument(
        "--lua",
        default=DEFAULT_LUA,
        help=f"Lua executable for runtime checks (default: {DEFAULT_LUA}).",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=os.cpu_count() or 1,
        help="Number of tests to run concurrently.",
    )
    return parser.parse_args()


def load_manifest():
    with open(TEST_TOML_PATH, "rb") as f:
        config = tomllib.load(f)
    tests = config.get("tests")
    if not isinstance(tests, dict):
        raise ValueError("tests/test.toml must contain a [tests] table")
    return tests


def validate_manifest(tests):
    errors = []
    referenced_hern_files = set()
    for name, test in tests.items():
        if not isinstance(test, dict):
            errors.append(f"{name}: test entry must be a table")
            continue

        unknown = set(test) - ALLOWED_KEYS
        if unknown:
            errors.append(f"{name}: unknown keys: {', '.join(sorted(unknown))}")

        path = test.get("path")
        if not isinstance(path, str) or not path:
            errors.append(f"{name}: `path` must be a non-empty string")
        else:
            referenced_hern_files.add(os.path.normpath(path))
            if not os.path.exists(os.path.join(REPO_ROOT, path)):
                errors.append(f"{name}: path does not exist: {path}")

        expect = test.get("expect")
        if expect not in ALLOWED_EXPECTS:
            errors.append(
                f"{name}: `expect` must be one of {', '.join(sorted(ALLOWED_EXPECTS))}"
            )

        if "output" in test and expect == "error":
            errors.append(f"{name}: error tests must not specify `output`")
        if "error_contains" in test and expect != "error":
            errors.append(f"{name}: only error tests may specify `error_contains`")

        tags = test.get("tags", [])
        if not isinstance(tags, list) or not all(isinstance(tag, str) for tag in tags):
            errors.append(f"{name}: `tags` must be a list of strings")

        fixtures = test.get("fixtures", [])
        if not isinstance(fixtures, list) or not all(
            isinstance(fixture, str) for fixture in fixtures
        ):
            errors.append(f"{name}: `fixtures` must be a list of strings")
        else:
            for fixture in fixtures:
                referenced_hern_files.add(os.path.normpath(fixture))
                if not os.path.exists(os.path.join(REPO_ROOT, fixture)):
                    errors.append(f"{name}: fixture does not exist: {fixture}")

        purpose = test.get("purpose")
        if purpose is not None and not isinstance(purpose, str):
            errors.append(f"{name}: `purpose` must be a string")

    hern_dir = os.path.join(REPO_ROOT, "tests", "hern")
    for filename in os.listdir(hern_dir):
        if not filename.endswith(".hern"):
            continue
        rel_path = os.path.normpath(os.path.join("tests", "hern", filename))
        if rel_path not in referenced_hern_files:
            errors.append(
                f"{rel_path}: Hern test file is not listed as a test or fixture"
            )

    if errors:
        joined = "\n  - ".join(errors)
        raise ValueError(f"invalid test manifest:\n  - {joined}")


def selected_tests(tests, patterns, tags):
    selected = []
    wanted_tags = set(tags)
    for name, test in tests.items():
        if patterns and not any(pattern in name for pattern in patterns):
            continue
        if wanted_tags and not wanted_tags.issubset(test_tags(name, test)):
            continue
        selected.append((name, test))
    return selected


def test_tags(name, test):
    tags = set(test.get("tags", []))
    tags.add(test["expect"])
    if "output" in test:
        tags.add("runtime")
    else:
        tags.add("compile")

    prefix_tags = [
        ("mut_param", "mutability"),
        ("mut_map", "mutability"),
        ("mut_", "mutability"),
        ("module_", "modules"),
        ("applied_impl", "impls"),
        ("inherent_applied", "methods"),
        ("associated", "methods"),
        ("receiver_method", "methods"),
        ("inherent_", "methods"),
        ("operator", "operators"),
        ("custom_op", "operators"),
        ("fixity", "operators"),
        ("multi_trait", "operators"),
        ("bare_", "traits"),
        ("trait_", "traits"),
        ("missing_trait", "traits"),
        ("ambiguous_trait", "traits"),
        ("pattern", "patterns"),
        ("tuple_", "patterns"),
        ("record_pattern", "patterns"),
        ("exhaustive_", "patterns"),
        ("let_destructure", "patterns"),
        ("expected_type", "inference"),
        ("propagate_constraints", "inference"),
        ("explicit_constraints", "inference"),
        ("constrained_lambdas", "inference"),
        ("inferred_", "inference"),
        ("lambda", "inference"),
        ("pipe", "syntax"),
        ("for_", "control-flow"),
        ("return_", "control-flow"),
        ("loop_", "control-flow"),
        ("never_", "control-flow"),
        ("prelude_", "prelude"),
        ("lua_std", "prelude"),
        ("std_", "prelude"),
    ]
    for prefix, tag in prefix_tags:
        if name.startswith(prefix):
            tags.add(tag)
    return tags


def build_hern():
    print("Building hern...")
    subprocess.run(["cargo", "build", "-p", "hern"], cwd=REPO_ROOT, check=True)
    return os.path.join(REPO_ROOT, "target", "debug", "hern")


def run_test(name, test, hern_bin, lua_bin):
    path = os.path.join(REPO_ROOT, test["path"])
    expect = test["expect"]

    command = "test" if expect == "test" else "lua"
    result = subprocess.run([hern_bin, command, path], capture_output=True, text=True)

    if expect == "error":
        if result.returncode == 0:
            return False, "Expected error but succeeded"
        error_contains = test.get("error_contains")
        if error_contains and error_contains not in result.stderr:
            return False, f"Error mismatch. Expected: {error_contains}, Got: {result.stderr}"
        return True, "Correctly rejected"

    if result.returncode != 0:
        return False, f"Compilation failed: {result.stderr}"

    if "output" in test:
        expected_output = test["output"]
        if expect == "test":
            actual_output = result.stdout
        else:
            rt = subprocess.run(
                [lua_bin, "-"], input=result.stdout, capture_output=True, text=True
            )
            if rt.returncode != 0:
                return False, f"Runtime error: {rt.stderr}"
            actual_output = rt.stdout
        if actual_output.strip() != expected_output.strip():
            return (
                False,
                "Output mismatch.\n"
                f"{format_output_mismatch(expected_output, actual_output)}",
            )

    return True, "Passed"


def list_tests(tests):
    for name, test in tests:
        tags = ", ".join(sorted(test_tags(name, test)))
        suffix = f" [{tags}]" if tags else ""
        print(f"{name}: {test['expect']} {test['path']}{suffix}")


def format_output_mismatch(expected, actual):
    expected_lines = expected.strip().splitlines()
    actual_lines = actual.strip().splitlines()
    width = len(str(max(len(expected_lines), len(actual_lines), 1)))
    lines = ["Expected:"]
    lines.extend(
        f"  {idx:>{width}} | {line}"
        for idx, line in enumerate(expected_lines, start=1)
    )
    lines.append("Got:")
    lines.extend(
        f"  {idx:>{width}} | {line}" for idx, line in enumerate(actual_lines, start=1)
    )
    for idx, (expected_line, actual_line) in enumerate(
        zip(expected_lines, actual_lines), start=1
    ):
        if expected_line != actual_line:
            lines.append(f"First differing line: {idx}")
            break
    else:
        if len(expected_lines) != len(actual_lines):
            lines.append(
                f"Line count differs: expected {len(expected_lines)}, got {len(actual_lines)}"
            )
    return "\n".join(lines)


def run_tests(tests, lua_bin, jobs):
    hern_bin = build_hern()
    workers = max(1, jobs)
    results = {}
    with ThreadPoolExecutor(max_workers=workers) as executor:
        futures = {
            executor.submit(run_test, name, test, hern_bin, lua_bin): name
            for name, test in tests
        }
        for future in as_completed(futures):
            name = futures[future]
            results[name] = future.result()

    passed = 0
    failed = 0
    for name in sorted(results):
        ok, msg = results[name]
        if ok:
            print(f"  \033[32m✓\033[0m {name}: {msg}")
            passed += 1
        else:
            print(f"  \033[31m✗\033[0m {name}: {msg}")
            failed += 1

    print(f"\n{passed} passed, {failed} failed")
    if failed > 0:
        sys.exit(1)


def main():
    args = parse_args()
    tests = load_manifest()
    validate_manifest(tests)
    selected = selected_tests(tests, args.patterns, args.tag)

    if not selected:
        print("No tests matched.", file=sys.stderr)
        sys.exit(1)

    if args.list:
        list_tests(selected)
    else:
        run_tests(selected, args.lua, args.jobs)


if __name__ == "__main__":
    main()
