/-
══════════════════════════════════════════════════════════════════════════════
  MAG P ≠ NP:
══════════════════════════════════════════════════════════════════════════════

  File: mag\Main.lean
  Author: Masaru Numagaki
  Date: January 2026
  Version: 1.0

  OVERVIEW:
  ─────────────────────────────────────────────────────────────────────────
  This file serves as the entry point. It imports all modules:
    - Core/    : Main theorems (sorry = 0, axiom = 0) - CLAIMS
    - Support/ : Auxiliary modules (sorry = 0, axiom = 0) - SUPPORT
    - Blueprint/: Design documents (may have axioms) - REFERENCE

  CORE THEOREMS:
  ─────────────────────────────────────────────────────────────────────────
  1. MAG_P_neq_NP (Theorem 3.1)
     - MAG internal separation theorem
     - Unconditional, sorry-free

  2. A5_Universal_Barrier (Theorem 4.6)
     - No solvable system can describe A₅-containing structures
     - Unconditional, sorry-free

  3. solvable_vanishing_depth (Theorem 4.7)
     - Commutator trees vanish beyond derived length
     - Unconditional, sorry-free

  4. Bridge_P_neq_NP (Theorem 5.4)
     - If TranslationInterface holds, then P ≠ NP
     - Conditional, sorry-free

  5. BarringtonToy_P_neq_NP (Theorem 5.7)
     - End-to-end toy verification
     - Unconditional, sorry-free

  PROOF STATUS:
  ┌──────────────────────────────────────────────────────────────────────┐
  │  Core/ directory: sorry = 0, axiom = 0                              │
  │  Support/ directory: sorry = 0, axiom = 0                           │
  │  All 5 theorems verified                                             │
  └──────────────────────────────────────────────────────────────────────┘

══════════════════════════════════════════════════════════════════════════════
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- CORE MODULE: Main Claims (sorry = 0, axiom = 0)
-- ═══════════════════════════════════════════════════════════════════════════

import MAG.Core.MAG_P_neq_NP
import MAG.Core.A5_Barrier
import MAG.Core.BarringtonBarrier
import MAG.Core.Bridge.Interface
import MAG.Core.Bridge.Theorem
import MAG.Core.Bridge.ToyInstantiation

-- ═══════════════════════════════════════════════════════════════════════════
-- SUPPORT / BLUEPRINT: Build separately
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Support and Blueprint are NOT imported here.
-- Build them separately:
--   lake build Support   -- Appendix A (sorry = 0, axiom = 0)
--   lake build Blueprint -- Appendix B (contains axioms)
--

namespace MAG

/-!
══════════════════════════════════════════════════════════════════════════════
  MAIN THEOREM VERIFICATION
══════════════════════════════════════════════════════════════════════════════
-/

section MainTheorems

-- Theorem 3.1: MAG internal separation (unconditional)
#check MAG.Core.MAG_P_neq_NP

-- Theorem 4.6: A₅ universal barrier (unconditional)
#check MAG.Core.A5_Universal_Barrier

-- Theorem 4.7: Commutator tree vanishing depth (unconditional)
#check MAG.Core.BarringtonBarrier.CommTerm.solvable_vanishing_depth

-- Theorem 5.4: Bridge theorem (conditional)
#check MAG.Core.Bridge.Bridge_P_neq_NP

-- Theorem 5.7: Toy model verification (unconditional)
#check MAG.Core.Bridge.BarringtonToy_P_neq_NP

end MainTheorems

/-!
══════════════════════════════════════════════════════════════════════════════
  AXIOM VERIFICATION
══════════════════════════════════════════════════════════════════════════════

  The following #print axioms commands verify that the Core theorems
  do NOT depend on any custom axioms (only standard Lean/Mathlib axioms
  like propext, Quot.sound, Classical.choice are expected).

══════════════════════════════════════════════════════════════════════════════
-/

section AxiomVerification

-- Theorem 3.1: MAG internal separation
-- Expected output: 'MAG.Core.MAG_P_neq_NP' depends on axioms: [propext, ...]
#print axioms MAG.Core.MAG_P_neq_NP

-- Theorem 4.6: A₅ universal barrier
#print axioms MAG.Core.A5_Universal_Barrier

-- Theorem 4.7: Commutator tree vanishing depth
#print axioms MAG.Core.BarringtonBarrier.CommTerm.solvable_vanishing_depth

-- Theorem 5.4: Bridge theorem (conditional on TranslationInterface)
#print axioms MAG.Core.Bridge.Bridge_P_neq_NP

-- Theorem 5.7: Toy model verification
#print axioms MAG.Core.Bridge.BarringtonToy_P_neq_NP

end AxiomVerification

/-!
══════════════════════════════════════════════════════════════════════════════
  DIRECTORY STRUCTURE
══════════════════════════════════════════════════════════════════════════════

  MAG/
  ├── Main.lean                      ← This file (entry point)
  ├── lakefile.toml                  ← Lake build configuration
  ├── lean-toolchain                 ← Lean version (4.27.0-rc1)
  ├── LICENSE                        ← Apache-2.0
  ├── README.md                      ← Project documentation
  │
  ├── Core/                          ★ sorry = 0, axiom = 0 (CLAIMS)
  │   ├── MAG_P_neq_NP.lean          (Theorem 3.1)
  │   ├── A5_Barrier.lean            (Theorem 4.6)
  │   ├── BarringtonBarrier.lean     (Theorem 4.7)
  │   └── Bridge/
  │       ├── Interface.lean         (Definitions 5.1-5.5)
  │       ├── Theorem.lean           (Theorem 5.4)
  │       └── ToyInstantiation.lean  (Theorem 5.7)
  │
  ├── Support/                       ★ sorry = 0, axiom = 0 (AUXILIARY)
  │   ├── Barrington/
  │   │   ├── Complete.lean
  │   │   └── Arithmetic.lean
  │   ├── Circuits/
  │   │   └── KrohnRhodes.lean
  │   └── Syntactic/
  │       └── Theory.lean
  │
  └── Blueprint/                     ★ Design documents (may have axioms)
      ├── StandardModel/
      └── Alternative/

══════════════════════════════════════════════════════════════════════════════
-/

end MAG
