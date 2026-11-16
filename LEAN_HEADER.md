# Lean module header

This rule binds every bot, Grok agent, and GitHub Actions job that writes a Lean module under Benjamin Stanley Frohman.

The name does not go after the import. It goes in the copyright block, and that block is the first thing in the file. The module docstring comes after the imports, and its first line is a `#` heading.

```lean
/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Module.Name

What this module actually proves.
-/
```

`/-!` is a Lean command. It is valid after the imports. It is not a substitute for the copyright block, and it does not take `Author:`, `Date:`, or `License:` lines.

The authors line is exactly `Authors: Benjamin Stanley Frohman`. One author, no "and", no trailing period.

Commits use author Benjamin Stanley Frohman, email frohmanbenjamin@gmail.com. Do not add a `Co-authored-by: Grok` trailer.

A file whose copyright names someone other than Frohman is left alone.

`.github/workflows/lean-header.yml` runs `python3 scripts/lean_header.py --check .` on push and on `workflow_dispatch`.
