import Lake
open Lake DSL

package MAG where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

/-!
═══════════════════════════════════════════════════════════════════════════
  MAG P≠NP:
═══════════════════════════════════════════════════════════════════════════

  LIBRARY STRUCTURE:
  ─────────────────────────────────────────────────────────────────────────
  Core/     : Main claims (sorry=0, axiom=0) - CLAIMS
  Support/  : Auxiliary modules (sorry=0, axiom=0) - SUPPORT
  Blueprint/: Design documents (may have axioms) - REFERENCE
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- CORE LIBRARY: Main Claims (default target)
-- ═══════════════════════════════════════════════════════════════════════════
-- Build with: lake build
-- Status: sorry = 0, axiom = 0

@[default_target]
lean_lib Core where
  globs := #[.submodules `MAG.Core]

-- ═══════════════════════════════════════════════════════════════════════════
-- SUPPORT LIBRARY:
-- ═══════════════════════════════════════════════════════════════════════════
-- Build with: lake build Support
-- Status: sorry = 0, axiom = 0

lean_lib Support where
  globs := #[.submodules `MAG.Support]

-- ═══════════════════════════════════════════════════════════════════════════
-- BLUEPRINT LIBRARY:
-- ═══════════════════════════════════════════════════════════════════════════
-- Build with: lake build Blueprint
-- Status: contains axioms (external theorem representations)

lean_lib Blueprint where
  globs := #[.submodules `MAG.Blueprint]

-- ═══════════════════════════════════════════════════════════════════════════
-- MAIN ENTRY POINT: Core + verification #checks
-- ═══════════════════════════════════════════════════════════════════════════
-- Build with: lake build MAG

lean_lib MAG where
  roots := #[`MAG.Main]
