import Mathlib
import Formalism.LocalRingCardinality.Params

namespace GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria
open Formalism.BasicNotions

universe u v

def PartsSum (R : Ranks) {FT : Type u} (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)]
    (part : ∀ j, FT → Submodule ℂ (M j)) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → iSupIndep (part j) ∧ ⨆ π, part j π = ⊤

def PartsSumIn (R : Ranks) {FT : Type u} (A : ℕ → Type v) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    (M : ∀ j, Submodule ℂ (A j)) (part : ∀ j, FT → Submodule ℂ (A j)) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → iSupIndep (part j) ∧ ⨆ π, part j π = M j

theorem partsSum_iff_isInternal (R : Ranks) {FT : Type u} [DecidableEq FT] (M : ℕ → Type v)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] (part : ∀ j, FT → Submodule ℂ (M j)) :
    PartsSum R M part ↔ ∀ j : ℕ, 1 ≤ j → j ≤ R.m → DirectSum.IsInternal (part j) := by
  simp only [PartsSum, DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]

theorem partsSum_iff_partsSumIn_top (R : Ranks) {FT : Type u} (M : ℕ → Type v)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] (part : ∀ j, FT → Submodule ℂ (M j)) :
    PartsSum R M part ↔ PartsSumIn R M (fun _ => ⊤) part := Iff.rfl

theorem partsSum_plane (R : Ranks) :
    PartsSum R (fun _ => ℂ × ℂ)
      (fun _ (b : Bool) => cond b (LinearMap.range (LinearMap.inl ℂ ℂ ℂ)) (LinearMap.range (LinearMap.inr ℂ ℂ ℂ))) := by
  intro j _ _
  have h := LinearMap.isCompl_range_inl_inr (R := ℂ) (M := ℂ) (M₂ := ℂ)
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_pair (i := true) (j := false) (by simp) (by intro k; cases k <;> simp)]
    exact h.disjoint
  · rw [iSup_bool_eq]
    exact h.sup_eq_top

theorem not_partsSum_repeated (R : Ranks) :
    ¬ PartsSum R (fun _ => ℂ) (fun _ (_ : Bool) => (⊤ : Submodule ℂ ℂ)) := by
  intro h
  have h1 := (h 1 le_rfl (by have := R.two_le_m; omega)).1
  rw [iSupIndep_pair (i := true) (j := false) (by simp) (by intro k; cases k <;> simp)] at h1
  simp at h1

theorem not_partsSum_zero (R : Ranks) :
    ¬ PartsSum R (fun _ => ℂ) (fun _ (_ : Unit) => (⊥ : Submodule ℂ ℂ)) := by
  intro h
  have h1 := (h 1 le_rfl (by have := R.two_le_m; omega)).2
  simp at h1

end GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria
