/-
══════════════════════════════════════════════════════════════════════════════
  BARRINGTON BARRIER: VANISHING DEPTH FOR SOLVABLE GROUPS
══════════════════════════════════════════════════════════════════════════════

  File: mag\core\BarringtonBarrier.lean
  Author: Masaru Numagaki
  Date: January 2026
  Version: 1.0

  PAPER CORRESPONDENCE:
  ─────────────────────────────────────────────────────────────────────────
  Section 4.7: Commutator Tree Vanishing Depth
  ─────────────────────────────────────────────────────────────────────────

  KEY INSIGHT:
  Commutator trees (not self-commutator recursion) provide the correct
  formalization of depth barriers:

      depth 0: a variable
      depth n+1: a commutator of two depth-n terms

  The key lemma: eval(term of depth n) ∈ derivedSeries G n.

  Hence if G is solvable with derived length k (derivedSeries G k = ⊥),
  every term of depth ≥ k evaluates to 1 (identity).

  PROOF STATUS:
  ┌──────────────────────────────────────────────────────────────────────┐
  │  ✅ COMPLETE: sorry = 0, axiom = 0                                  │
  └──────────────────────────────────────────────────────────────────────┘

══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Nat.Basic

namespace MAG.Core.BarringtonBarrier

universe u

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 1: COMMUTATOR TREES (BALANCED)
══════════════════════════════════════════════════════════════════════════════

  `CommTerm α n` is a *balanced commutator expression* of depth `n`
  with leaves labelled by `α`.
-/

/--
  **Definition: Commutator Term**

  A balanced binary tree where:
  - Leaves (depth 0): variables from α
  - Internal nodes (depth n+1): commutators of two depth-n terms
-/
inductive CommTerm (α : Type u) : ℕ → Type u
  | var : α → CommTerm α 0
  | comm {n : ℕ} : CommTerm α n → CommTerm α n → CommTerm α (n+1)

namespace CommTerm

variable {α : Type u}
variable {G : Type u} [Group G]

/-- Evaluate a commutator term under an assignment `ρ : α → G`. -/
def eval (ρ : α → G) : {n : ℕ} → CommTerm α n → G
  | 0,   var x      => ρ x
  | _+1, comm t u   => ⁅eval ρ t, eval ρ u⁆

@[simp] lemma eval_var (ρ : α → G) (x : α) : eval ρ (var x) = ρ x := rfl

@[simp] lemma eval_comm (ρ : α → G) {n : ℕ} (t u : CommTerm α n) :
    eval ρ (comm t u) = ⁅eval ρ t, eval ρ u⁆ := rfl


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 2: DEPTH RESPECTS THE DERIVED SERIES
══════════════════════════════════════════════════════════════════════════════

  This is the formal core:
    depth n commutator-terms always land in `derivedSeries G n`.
-/

/--
  **Theorem: Commutator Depth → Derived Series Membership**

  For any commutator term t of depth n, eval(t) ∈ derivedSeries G n.
-/
theorem eval_mem_derivedSeries (ρ : α → G) :
    ∀ {n : ℕ} (t : CommTerm α n), eval ρ t ∈ derivedSeries G n := by
  intro n t
  induction t with
  | var x =>
      -- derivedSeries G 0 = ⊤
      simp [derivedSeries]
  | comm t u ih_t ih_u =>
      -- derivedSeries G (n+1) = ⁅derivedSeries G n, derivedSeries G n⁆
      simp only [eval_comm, derivedSeries]
      exact Subgroup.commutator_mem_commutator ih_t ih_u


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 3: DERIVED SERIES STABILITY
══════════════════════════════════════════════════════════════════════════════

  Once derivedSeries hits ⊥, it stays ⊥.
-/

theorem derivedSeries_eq_bot_of_ge {k n : ℕ}
    (hk : derivedSeries G k = ⊥) (hkn : k ≤ n) : derivedSeries G n = ⊥ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  induction m with
  | zero => simp [hk]
  | succ m ih =>
      simp [derivedSeries, ih]


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 4: VANISHING DEPTH THEOREM FOR SOLVABLE GROUPS
══════════════════════════════════════════════════════════════════════════════

  If G is solvable, there exists a finite depth threshold beyond which
  **every** commutator-tree computation collapses to the identity.
-/

/--
  **Theorem 4.7: Solvable Vanishing Depth**

  For any solvable group G, there exists k such that all commutator trees
  of depth ≥ k evaluate to the identity element.

  This is the "Barrier Lemma" for Barrington-style depth analysis.
-/
theorem solvable_vanishing_depth {G : Type u} [Group G] [IsSolvable G] :
    ∃ k : ℕ, ∀ {α : Type u} (ρ : α → G) {n : ℕ}, k ≤ n →
      ∀ (t : CommTerm α n), eval ρ t = 1 := by
  -- solvable ⇔ ∃k, derivedSeries G k = ⊥
  obtain ⟨k, hk⟩ : ∃ k : ℕ, derivedSeries G k = ⊥ :=
    (inferInstance : IsSolvable G).solvable
  refine ⟨k, ?_⟩
  intro α ρ n hkn t
  have hmem : eval ρ t ∈ derivedSeries G n :=
    eval_mem_derivedSeries (G := G) (ρ := ρ) t
  have hn : derivedSeries G n = ⊥ :=
    derivedSeries_eq_bot_of_ge (G := G) hk hkn
  rw [hn] at hmem
  exact Subgroup.mem_bot.mp hmem

end CommTerm


/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 5: THE A₅ CONTRAST (NON-VANISHING)
══════════════════════════════════════════════════════════════════════════════

  For the paper narrative, the complementary fact is that A₅ never vanishes:
  its derived series is constantly ⊤ (perfectness).

  This does *not* claim that every commutator term is nontrivial; it only
  establishes that A₅ has no finite derived-length threshold.
-/

abbrev A5 := alternatingGroup (Fin 5)

/-- A₅ is perfect: [A₅, A₅] = A₅ -/
theorem A5_commutator_eq_top : commutator A5 = ⊤ := by
  have h_simple : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup_five
  have h_not_solvable : ¬ IsSolvable A5 := by
    rw [← IsSimpleGroup.comm_iff_isSolvable]
    intro h_comm
    let σ : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
                   Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    let τ : A5 := ⟨Equiv.swap 1 2 * Equiv.swap 3 4,
                   Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    have h_ne : σ * τ ≠ τ * σ := by
      rw [Ne, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
      decide
    exact h_ne (h_comm σ τ)
  have h_normal : (commutator A5).Normal := Subgroup.commutator_normal ⊤ ⊤
  cases h_normal.eq_bot_or_eq_top with
  | inl h_bot =>
      have : IsSolvable A5 := isSolvable_of_comm (fun x y =>
        commutatorElement_eq_one_iff_commute.mp
          (Subgroup.mem_bot.mp (h_bot.symm ▸
            Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))))
      contradiction
  | inr h_top => exact h_top

/-- A₅ derived series is constantly ⊤. -/
theorem A5_derivedSeries_top (n : ℕ) : derivedSeries A5 n = ⊤ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [derivedSeries_succ, ih]
      change commutator A5 = ⊤
      exact A5_commutator_eq_top

/-- A₅ has no finite vanishing depth. -/
theorem A5_no_vanishing_depth : ¬ ∃ k : ℕ, derivedSeries A5 k = ⊥ := by
  rintro ⟨k, hk⟩
  have : (⊤ : Subgroup A5) = (⊥ : Subgroup A5) := by
    rw [← A5_derivedSeries_top k, hk]
  exact top_ne_bot this


/-!
══════════════════════════════════════════════════════════════════════════════
  SUMMARY
══════════════════════════════════════════════════════════════════════════════

  ┌────────────────────────────────────────────────────────────────────────┐
  │  THEOREM: Solvable Vanishing Depth                                    │
  │                                                                        │
  │  For solvable G: ∃ k, ∀ depth-n tree (n ≥ k), eval = 1               │
  │                                                                        │
  │  CONTRAST:                                                            │
  │  For A₅: ∀ n, derivedSeries A₅ n = ⊤ (no vanishing)                  │
  │                                                                        │
  │  STATUS: sorry = 0, axiom = 0                                         │
  └────────────────────────────────────────────────────────────────────────┘
══════════════════════════════════════════════════════════════════════════════
-/

end MAG.Core.BarringtonBarrier
