# CI checks

`Build project` validates Lean, including utility tests, the combined `All` module,
and category warnings. Its name is retained for existing branch protection.
`Build documentation` runs afterward on a separate runner when the existing site
path rules require it. Deployment waits for Lean, documentation, and script tests.
A documentation failure does not change the completed Lean check's result.
Maintainers who require documentation before merging should require the separate
`Build documentation` check as well.

The prepared environment cache contains the installed Lean toolchain and dependency
sources and builds. Its exact key includes the platform, toolchain, dependency
manifest, and Lake configuration. A miss uses the Mathlib download path. Successful
main pushes populate this cache; PRs only restore it. The first main run after this
change will populate it, so a PR before then does not measure warm-cache speed.

The project cache is saved after Lean validation and metadata extraction. It is
separate from the documentation caches, so documentation cannot invalidate the
next PR's Lean artifacts. Lake still checks dependencies and rebuilds affected
modules; no validation is skipped based on the changed-file list.

To measure the effect, compare actual one-file PRs against the same populated base.
Record queue delay, prepared environment restoration, project cache restoration,
and time until `Build project` completes. Repeat several times. The larger
prepared cache must restore faster than the setup it replaces to be worthwhile.
