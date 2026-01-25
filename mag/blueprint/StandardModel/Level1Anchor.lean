/-
══════════════════════════════════════════════════════════════════════════════
  STANDARD MODEL LEVEL 1 ANCHOR: S5 → A5 BRIDGE
══════════════════════════════════════════════════════════════════════════════

  File: mag\blueprint\StandardModel\Level1Anchor.lean
  Author: Masaru Numagaki
  Date: January 2026
  Version: 1.0

  PURPOSE:
  ─────────────────────────────────────────────────────────────────────────
  Connects the "S5 Anchor" (closer to Barrington's raw theorem)
  to the "A5 Anchor" (required by the bridge).

══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace MAG.Blueprint.StandardModel.Level1Anchor

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 1: BASIC DEFINITIONS
══════════════════════════════════════════════════════════════════════════════
-/

abbrev S5 := Equiv.Perm (Fin 5)
abbrev A5 := alternatingGroup (Fin 5)

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 2: A5 AS INDEX-2 SUBGROUP OF S5
══════════════════════════════════════════════════════════════════════════════
-/

/-- |A₅| = 60 -/
theorem A5_card : Fintype.card A5 = 60 := by native_decide

/-- |S₅| = 120 -/
theorem S5_card : Fintype.card S5 = 120 := by native_decide

/-- A₅ has index 2 in S₅ -/
theorem A5_index_in_S5 : (alternatingGroup (Fin 5)).index = 2 := by
  have hcard : Nat.card A5 * (alternatingGroup (Fin 5)).index = Nat.card S5 :=
    Subgroup.card_mul_index (alternatingGroup (Fin 5))
  simp only [Nat.card_eq_fintype_card, A5_card, S5_card] at hcard
  omega

/-- The canonical injection A₅ ↪ S₅ -/
def A5_to_S5 : A5 →* S5 := (alternatingGroup (Fin 5)).subtype

theorem A5_to_S5_injective : Function.Injective A5_to_S5 :=
  Subtype.coe_injective

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 3: ABSTRACT COMPUTATIONAL MODEL (MINIMAL)
══════════════════════════════════════════════════════════════════════════════
-/

/-- Abstract computational model interface -/
class ComputationalModel (M : Type*) where
  Problem : Type*
  Algorithm : Type*
  problemSymmetry : Problem → Type*
  [problemGroup : ∀ p, Group (problemSymmetry p)]
  [problemFintype : ∀ p, Fintype (problemSymmetry p)]
  algorithmOperations : Algorithm → Type*
  [algorithmGroup : ∀ a, Group (algorithmOperations a)]
  [algorithmFintype : ∀ a, Fintype (algorithmOperations a)]
  solves : Algorithm → Problem → Prop
  isPolyTime : Algorithm → Prop
  isNPHard : Problem → Prop

attribute [instance] ComputationalModel.problemGroup ComputationalModel.problemFintype
attribute [instance] ComputationalModel.algorithmGroup ComputationalModel.algorithmFintype

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 4: ANCHOR CLASSES
══════════════════════════════════════════════════════════════════════════════
-/

/--
  ANCHOR (S5 version):
  NP-hardness implies an embedding of the full symmetric group S5.
-/
class Level1S5Anchor (M : Type*) [ComputationalModel M] : Prop where
  nphard_has_S5 :
    ∀ (p : ComputationalModel.Problem (M := M)),
      ComputationalModel.isNPHard (M := M) p →
        ∃ (f : S5 →* ComputationalModel.problemSymmetry (M := M) p),
          Function.Injective f

/--
  ANCHOR (A5 version):
  NP-hardness implies an embedding of the alternating group A5.
-/
class BarringtonNPAnchor (M : Type*) [ComputationalModel M] : Prop where
  nphard_has_A5 :
    ∀ (p : ComputationalModel.Problem (M := M)),
      ComputationalModel.isNPHard (M := M) p →
        ∃ (f : A5 →* ComputationalModel.problemSymmetry (M := M) p),
          Function.Injective f

/--
  AUTOMATIC INSTANCE:
  If a model has the S5 anchor, it automatically has the A5 anchor
  (since A5 injects into S5).
-/
instance (M : Type*) [ComputationalModel M] [Level1S5Anchor M] : BarringtonNPAnchor M where
  nphard_has_A5 := by
    intro p hp
    obtain ⟨f_S5, h_inj_S5⟩ := Level1S5Anchor.nphard_has_S5 p hp
    let i : A5 →* S5 := A5_to_S5
    have h_inj_i : Function.Injective i := A5_to_S5_injective
    exact ⟨f_S5.comp i, h_inj_S5.comp h_inj_i⟩

/-!
══════════════════════════════════════════════════════════════════════════════
  SECTION 5: VERIFICATION
══════════════════════════════════════════════════════════════════════════════
-/

theorem level1_anchor_summary :
    (Fintype.card A5 = 60) ∧
    (Fintype.card S5 = 120) ∧
    ((alternatingGroup (Fin 5)).index = 2) ∧
    (Function.Injective A5_to_S5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact A5_card
  · exact S5_card
  · exact A5_index_in_S5
  · exact A5_to_S5_injective

end MAG.Blueprint.StandardModel.Level1Anchor
