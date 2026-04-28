#!/usr/bin/env python3
import os
import subprocess
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor, as_completed

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEST_TOML_PATH = os.path.join(REPO_ROOT, "tests", "test.toml")
LUA = "luajit" # Or "lua"

def build_hern():
    print("Building hern...")
    subprocess.run(["cargo", "build", "-p", "hern"], cwd=REPO_ROOT, check=True)
    return os.path.join(REPO_ROOT, "target", "debug", "hern")

def run_test(name, test, hern_bin):
    path = os.path.join(REPO_ROOT, test["path"])
    expect = test["expect"]
    
    # Run typecheck/lua generation
    result = subprocess.run([hern_bin, "lua", path], capture_output=True, text=True)
    
    if expect == "error":
        if result.returncode == 0:
            return False, "Expected error but succeeded"
        error_contains = test.get("error_contains")
        if error_contains and error_contains not in result.stderr:
            return False, f"Error mismatch. Expected: {error_contains}, Got: {result.stderr}"
        return True, "Correctly rejected"
    
    if result.returncode != 0:
        return False, f"Compilation failed: {result.stderr}"
    
    lua_code = result.stdout
    if "output" in test:
        expected_output = test["output"]
        rt = subprocess.run([LUA, "-"], input=lua_code, capture_output=True, text=True)
        if rt.returncode != 0:
            return False, f"Runtime error: {rt.stderr}"
        if rt.stdout.strip() != expected_output.strip():
            return False, f"Output mismatch.\nExpected:\n{expected_output.strip()}\nGot:\n{rt.stdout.strip()}"
    
    return True, "Passed"

def main():
    hern_bin = build_hern()
    with open(TEST_TOML_PATH, "rb") as f:
        config = tomllib.load(f)
    
    tests = config.get("tests", {})

    results = {}
    with ThreadPoolExecutor() as executor:
        futures = {executor.submit(run_test, name, test, hern_bin): name for name, test in tests.items()}
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

if __name__ == "__main__":
    main()
