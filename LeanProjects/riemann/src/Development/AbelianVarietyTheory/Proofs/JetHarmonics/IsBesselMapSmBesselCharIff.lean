import Mathlib
import Formalism.PeriodIntegrals.BesselMapUniq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsWtOnIffOfTorus

open Matrix

noncomputable section

namespace GlobalTheory.BesselMapCompare

open PI.UpqRep GlobalTheory.IndefiniteRowSideFullHecke

def scaleEquiv (r : ℕ) : (Fin r → ℂ) ≃ (Fin r → ℂ) where
  toFun κ := fun a => -2 * Complex.I * κ a
  invFun c := fun a => Complex.I / 2 * c a
  left_inv κ := by
    funext a
    linear_combination (-κ a) * Complex.I_mul_I
  right_inv c := by
    funext a
    linear_combination (-c a) * Complex.I_mul_I

section Maps

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem isHCParam_of_isHCTypeW {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V)}
    (h : IsHCTypeW k r z u π) : PI.UpqRep.IsHCParam u := by
  obtain ⟨g, -, hg⟩ := h
  exact (KTypeCompare.isHCParam_iff u).2 ((KTypeCompare.isHCTypeU_iff u _).1 hg).param

end Maps

end GlobalTheory.BesselMapCompare

end
