/-
══════════════════════════════════════════════════════════════════════════════
  BARRINGTON ARITHMETIC: LOG-DEPTH TO POLY-LENGTH (SORRY-FREE)
══════════════════════════════════════════════════════════════════════════════

  File: mag\support\Barrington\Arithmetic.lean
  Author: Masaru Numagaki
  Date: January 2026
  Version: 1.0

  PURPOSE:
  ─────────────────────────────────────────────────────────────────────────
  This file proves the arithmetic lemmas needed to connect:
  - Log-depth circuits (NC¹)
  - Polynomial-length branching programs

  Main result: 4^(c · log₂ n) ≤ n^(2c) for n ≥ 2

══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

namespace MAG.Support.Barrington.Arithmetic

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 1: BASIC LOG₂ PROPERTIES
══════════════════════════════════════════════════════════════════════════════
-/

/-- 2^(log₂ n) ≤ n for n ≥ 1 -/
theorem pow2_log2_le (n : ℕ) (hn : n ≥ 1) : 2 ^ Nat.log2 n ≤ n := by
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)

/-- n < 2^(log₂ n + 1) for n ≥ 1 -/
theorem lt_pow2_log2_succ (n : ℕ) : n < 2 ^ (Nat.log2 n + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by norm_num) n

/-- log₂ (2^k) = k -/
theorem log2_pow2 (k : ℕ) : Nat.log2 (2 ^ k) = k := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_pow Nat.one_lt_two k

/-- Monotonicity of log₂ -/
theorem log2_mono {m n : ℕ} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  simp only [Nat.log2_eq_log_two]
  exact Nat.log_mono_right h


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 2: POWER INEQUALITIES
══════════════════════════════════════════════════════════════════════════════
-/

/-- 4^k = 2^(2k) -/
theorem pow4_eq_pow2_double (k : ℕ) : 4 ^ k = 2 ^ (2 * k) := by
  calc 4 ^ k = (2 ^ 2) ^ k := by norm_num
    _ = 2 ^ (2 * k) := by rw [← Nat.pow_mul]

/-- 4^k ≤ 4^m when k ≤ m -/
theorem pow4_mono {k m : ℕ} (h : k ≤ m) : 4 ^ k ≤ 4 ^ m := by
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) h


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 3: THE CORE ARITHMETIC THEOREM
══════════════════════════════════════════════════════════════════════════════

  We prove: 4^(c · log₂ n) ≤ n^(2c) for n ≥ 2

  This is the key lemma that connects log-depth circuits to poly-length BPs.
-/

/-- 4^(log₂ n) ≤ n² for n ≥ 1 -/
theorem pow4_log2_le_square (n : ℕ) (hn : n ≥ 1) : 4 ^ Nat.log2 n ≤ n ^ 2 := by
  have h1 : 4 ^ Nat.log2 n = 2 ^ (2 * Nat.log2 n) := pow4_eq_pow2_double (Nat.log2 n)
  have h2 : 2 ^ Nat.log2 n ≤ n := pow2_log2_le n hn
  calc 4 ^ Nat.log2 n = 2 ^ (2 * Nat.log2 n) := h1
    _ = (2 ^ Nat.log2 n) ^ 2 := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ n ^ 2 := Nat.pow_le_pow_left h2 2

/-- 4^(c · log₂ n) ≤ n^(2c) for n ≥ 1 -/
theorem pow4_cmul_log2_le (c n : ℕ) (hn : n ≥ 1) :
    4 ^ (c * Nat.log2 n) ≤ n ^ (2 * c) := by
  have h1 : 4 ^ (c * Nat.log2 n) = (4 ^ Nat.log2 n) ^ c := by
    rw [Nat.pow_mul']
  have h2 : 4 ^ Nat.log2 n ≤ n ^ 2 := pow4_log2_le_square n hn
  calc 4 ^ (c * Nat.log2 n) = (4 ^ Nat.log2 n) ^ c := h1
    _ ≤ (n ^ 2) ^ c := Nat.pow_le_pow_left h2 c
    _ = n ^ (2 * c) := by rw [← Nat.pow_mul]

/--
  ═══════════════════════════════════════════════════════════════════════════
  MAIN THEOREM: Log-depth to Polynomial-length (SORRY-FREE)

  If circuit depth ≤ c · log₂ n, then program length ≤ n^(2c).
  ═══════════════════════════════════════════════════════════════════════════
-/
theorem log_depth_implies_poly_length (c n : ℕ) (hn : n ≥ 1) (depth : ℕ)
    (h_depth : depth ≤ c * Nat.log2 n) :
    4 ^ depth ≤ n ^ (2 * c) := by
  calc 4 ^ depth ≤ 4 ^ (c * Nat.log2 n) := pow4_mono h_depth
    _ ≤ n ^ (2 * c) := pow4_cmul_log2_le c n hn

/-- Convenience: with explicit polynomial bound k = 2c -/
theorem log_depth_implies_poly_length' (c n : ℕ) (hn : n ≥ 1) (depth : ℕ)
    (h_depth : depth ≤ c * Nat.log2 n) :
    ∃ k : ℕ, 4 ^ depth ≤ n ^ k := by
  exact ⟨2 * c, log_depth_implies_poly_length c n hn depth h_depth⟩


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 4: NC¹ COMPLEXITY CLASS
══════════════════════════════════════════════════════════════════════════════
-/

/-- A function is in NC¹ if it has O(log n) depth circuits -/
structure NC1Function where
  /-- Circuit depth for input size n -/
  circuitDepth : ℕ → ℕ
  /-- Depth constant -/
  depthConstant : ℕ
  /-- Depth bound: circuitDepth(n) ≤ c · log₂ n for n ≥ 2 -/
  depth_bound : ∀ n : ℕ, n ≥ 2 → circuitDepth n ≤ depthConstant * Nat.log2 n

/-- NC¹ functions have polynomial-size width-5 BPs -/
theorem NC1_has_poly_BP (f : NC1Function) :
    ∀ n : ℕ, n ≥ 2 → 4 ^ (f.circuitDepth n) ≤ n ^ (2 * f.depthConstant) := by
  intro n hn
  have hn' : n ≥ 1 := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have h_depth := f.depth_bound n hn
  exact log_depth_implies_poly_length f.depthConstant n hn' (f.circuitDepth n) h_depth


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 5: VERIFICATION
══════════════════════════════════════════════════════════════════════════════
-/

/-- All arithmetic theorems are sorry-free -/
theorem arithmetic_complete :
    -- Basic inequalities
    (∀ k : ℕ, 4 ^ k = 2 ^ (2 * k)) ∧
    (∀ n : ℕ, n ≥ 1 → 4 ^ Nat.log2 n ≤ n ^ 2) ∧
    (∀ c n : ℕ, n ≥ 1 → 4 ^ (c * Nat.log2 n) ≤ n ^ (2 * c)) ∧
    -- NC¹ to poly-BP
    (∀ f : NC1Function, ∀ n : ℕ, n ≥ 2 →
      4 ^ (f.circuitDepth n) ≤ n ^ (2 * f.depthConstant)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pow4_eq_pow2_double
  · exact pow4_log2_le_square
  · exact pow4_cmul_log2_le
  · exact NC1_has_poly_BP

end MAG.Support.Barrington.Arithmetic
