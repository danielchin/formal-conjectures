#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0.
"""Partition problem sources by size and build one shard with Lake."""
import argparse
from pathlib import Path
import subprocess


def partition(files, count):
    if count < 1:
        raise ValueError("Shard count must be positive")
    groups = [[] for _ in range(count)]
    sizes = [0] * count
    # Source size is an initial cost estimate, not measured compilation time.
    for path in sorted(files, key=lambda p: (-p.stat().st_size, str(p))):
        index = min(range(count), key=lambda i: (sizes[i], i))
        groups[index].append(path)
        sizes[index] += path.stat().st_size
    return [sorted(group) for group in groups]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, required=True)
    parser.add_argument("--index", type=int, required=True)
    args = parser.parse_args()
    if not 0 <= args.index < args.count:
        parser.error("index must be between zero and count minus one")
    # All.lean is compiled only after collecting every shard's artifacts.
    files = [p for p in Path("FormalConjectures").rglob("*.lean")
             if p != Path("FormalConjectures/All.lean")]
    group = partition(files, args.count)[args.index]
    print(f"Shard {args.index}: {len(group)} of {len(files)} modules", flush=True)
    if not group:
        parser.error("empty shard; refusing to invoke Lake's default full build")
    # Lake accepts source paths, including numeric and Unicode filenames.
    raise SystemExit(subprocess.call([
        "python3", "scripts/lake-build-wrapper.py", f"/tmp/shard-{args.index}.json",
        "lake", "--wfail", "build", *map(str, group)]))


if __name__ == "__main__":
    main()
