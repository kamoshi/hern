# bench

End-to-end performance harness using [hyperfine](https://github.com/sharkdp/hyperfine).

Requires `brew install hyperfine`. Corpus is the files under `examples/`.

## Workflow

**1. Save a baseline** (do this on the branch you want to compare against):

```
./bench/run.sh save main
```

This copies the release binary into `bench/results/main/`.

**2. Make changes, rebuild:**

```
cargo build --release
```

**3. Compare:**

```
./bench/run.sh compare main
```

Runs both the saved binary and the current one side-by-side and prints a speedup ratio.

## Other commands

```
./bench/run.sh build   # cargo build --release
./bench/run.sh run     # run benchmarks without saving or comparing
```
