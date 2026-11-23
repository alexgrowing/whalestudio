import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def gam (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add, ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

def gam0 (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ (e k + e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add, ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

end GlobalTheory.Hk3.GramSep

end
