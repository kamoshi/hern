# bench

End-to-end performance harness using [hyperfine](https://github.com/sharkdp/hyperfine).

Requires `brew install hyperfine`. Corpus includes the files under `examples/`
plus generated synthetic files under `bench/corpus/`.

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
./bench/run.sh generate # generate synthetic benchmark corpus
./bench/run.sh run     # run benchmarks without saving or comparing
./bench/run.sh run-errors # run expected-failure recovery benchmarks
```

`bench/generate_synthetic.sh` is idempotent: it rewrites the same generated
corpus files each time. The generated files are intentionally not hand-edited.
