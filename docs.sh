#!/usr/bin/env bash
# Regenerate GeneralizationLinter docs fast (keeps Mathlib's doc cache).
set -euo pipefail
cd "$(dirname "$0")"                          # project root (holds docbuild/)
lake build GeneralizationLinter               # 1. compile edits into oleans
cd docbuild
rm -f .lake/build/doc-data/GeneralizationLinter*.doc.hash \
      .lake/build/doc-data/GeneralizationLinter*.doc.trace \
      .lake/build/doc-data/GeneralizationLinter--library.docs_built.*   # 2. bust your doc cache
DOCGEN_SRC=file lake build GeneralizationLinter:docs                     # 3. re-render (~30s)
echo "Done → serve docbuild/.lake/build/doc and hard-refresh (Cmd+Shift+R)"
