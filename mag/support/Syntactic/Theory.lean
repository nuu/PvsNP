/-
══════════════════════════════════════════════════════════════════════════════
  SYNTACTIC GROUP THEORY: THE FINAL BRIDGE
══════════════════════════════════════════════════════════════════════════════

  File: mag\support\Syntactic\Theory.lean
  Author: Masaru Numagaki
  Date: January 2026
  Version: 1.0

  PURPOSE:
  ─────────────────────────────────────────────────────────────────────────
  This file proves the "Fundamental Theorem of Syntactic Monoids" for groups:

    "The syntactic monoid of the word problem of a group G is isomorphic to G."

  This theorem justifies the final step of the MAG bridge:
    Barrington (Word Problem S5) → Syntactic Monoid → S5 → A5
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

namespace MAG.Support.Syntactic.Theory

section Definitions

variable {α : Type*}

/-- 1. Definition of Syntactic Congruence -/
def syntacticRel (L : List α → Prop) (u v : List α) : Prop :=
  ∀ x y : List α, L (x ++ u ++ y) ↔ L (x ++ v ++ y)

/-- Proof that syntactic congruence is an equivalence relation -/
theorem syntacticRel_equivalence (L : List α → Prop) : Equivalence (syntacticRel L) := by
  constructor
  · intro u x y; rfl
  · intro u v h x y; exact (h x y).symm
  · intro u v w h1 h2 x y; exact (h1 x y).trans (h2 x y)

/-- Setoid instance for syntactic congruence -/
instance syntacticSetoid (L : List α → Prop) : Setoid (List α) where
  r := syntacticRel L
  iseqv := syntacticRel_equivalence L

/-- 2. Definition of Syntactic Monoid: Σ* / ~L -/
def SyntacticMonoid (L : List α → Prop) := Quotient (syntacticSetoid L)

/-- Multiplication on Syntactic Monoid -/
def SyntacticMonoid.mul {L : List α → Prop} (q1 q2 : SyntacticMonoid L) : SyntacticMonoid L :=
  Quotient.lift₂ (s₁ := syntacticSetoid L) (s₂ := syntacticSetoid L)
    (f := fun u v => Quotient.mk (syntacticSetoid L) (u ++ v))
    (fun u1 v1 u2 v2 (hu : syntacticRel L u1 u2) (hv : syntacticRel L v1 v2) => by
      apply Quotient.sound
      intro x y
      show L (x ++ (u1 ++ v1) ++ y) ↔ L (x ++ (u2 ++ v2) ++ y)
      calc L (x ++ (u1 ++ v1) ++ y)
        _ ↔ L (x ++ u1 ++ (v1 ++ y)) := by simp only [List.append_assoc]
        _ ↔ L (x ++ u2 ++ (v1 ++ y)) := hu x (v1 ++ y)
        _ ↔ L ((x ++ u2) ++ v1 ++ y) := by simp only [List.append_assoc]
        _ ↔ L ((x ++ u2) ++ v2 ++ y) := hv (x ++ u2) y
        _ ↔ L (x ++ (u2 ++ v2) ++ y) := by simp only [List.append_assoc]
    ) q1 q2

/-- Monoid structure on the quotient set -/
instance instMonoidSyntacticMonoid (L : List α → Prop) : Monoid (SyntacticMonoid L) where
  mul := SyntacticMonoid.mul
  mul_assoc a b c := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    apply Quotient.sound
    intro x y
    simp only [List.append_assoc]
  one := (Quotient.mk (syntacticSetoid L) [])
  one_mul a := by
    induction a using Quotient.ind
    apply Quotient.sound
    intro x y
    simp
  mul_one a := by
    induction a using Quotient.ind
    apply Quotient.sound
    intro x y
    simp

end Definitions

section MainTheorem

variable {G : Type*} [Group G]

/-- The Word Problem of a group G -/
def WordProblem (w : List G) : Prop := (w.prod = 1)

/--
  3. Core Lemma: Syntactic congruence coincides with product equality.
-/
theorem syntactic_iff_prod_eq (u v : List G) :
    syntacticRel WordProblem u v ↔ u.prod = v.prod := by
  constructor
  · -- (⇒) Syntactic congruence implies equal products
    intro h
    specialize h [] [u.prod⁻¹]
    simp only [WordProblem, List.nil_append, List.prod_append, List.prod_singleton, mul_inv_cancel, true_iff] at h
    symm
    exact eq_of_mul_inv_eq_one h
  · -- (⇐) Equal products implies syntactic congruence
    intro h x y
    simp only [WordProblem, List.prod_append, h]

/--
  4. Main Theorem: The syntactic monoid of the word problem is isomorphic
     to the original group G.
-/
noncomputable def wordProblem_syntacticMonoid_iso_self :
    SyntacticMonoid (@WordProblem G _) ≃* G where
  toFun q := Quotient.lift (s := syntacticSetoid WordProblem) (f := fun w => w.prod)
      (fun a b h => (syntactic_iff_prod_eq a b).mp h) q
  invFun g := Quotient.mk (syntacticSetoid WordProblem) [g]
  left_inv q := by
    induction q using Quotient.ind
    case a w =>
      simp only [Quotient.lift_mk]
      apply Quotient.sound
      show syntacticRel WordProblem [w.prod] w
      rw [syntactic_iff_prod_eq]
      simp
  right_inv g := by
    simp only [Quotient.lift_mk, List.prod_singleton]
  map_mul' q1 q2 := by
    induction q1 using Quotient.ind; case a u =>
    induction q2 using Quotient.ind; case a v =>
    dsimp [HMul.hMul, Mul.mul, instMonoidSyntacticMonoid, SyntacticMonoid.mul]
    simp only [List.prod_append]
    rfl

end MainTheorem

end MAG.Support.Syntactic.Theory
