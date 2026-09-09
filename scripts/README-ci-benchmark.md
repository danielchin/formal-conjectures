# Narrow shared import experiment

This branch tests one shared module before a repository-wide import migration.
It uses the same Lean sources as commit `a01ac4b9227e2a540bf69dcda8580fbf413514b1`.

`FormalConjecturesUtil.SharedImports` contains the existing shared imports except
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey`. Problems 566, 567,
and 596 import that module directly. Mathlib imports and problem statements are
unchanged. The import linter allows specific shared modules but still rejects
the shared aggregate and direct Mathlib imports.

The common-import list is a snapshot for this experiment. It needs a generation
policy before this approach can be adopted throughout the repository.

Run `build-and-docs.yml` manually with `shards=1`:

1. `use_cache=false`, `shared_change=false`: validate and populate a cold cache.
2. `use_cache=true`, `shared_change=false`: measure an unchanged warm build.
3. `use_cache=true`, `shared_change=true`: change the graph Ramsey module's
   module docstring after restoring the original cache, then validate again.

The control is branch `codex/ci-shards-20260909`, with `shards=1` and the same
inputs. Compare critical-path time, actual rebuilt module counts, and cache
restore logs. A cold build does not measure avoided dependency invalidation.
The modified-source runs do not save caches, so they preserve the control cache.
Every run keeps shared-library tests, full problem compilation, the combined
`All.lean` collision check, and category validation. There is no website build
or deployment. A single sample per case is indicative, not conclusive.
