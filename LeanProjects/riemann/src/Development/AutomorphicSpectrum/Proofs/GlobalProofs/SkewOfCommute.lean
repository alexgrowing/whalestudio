import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DRepCEqDsigC
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie GlobalTheory.CompanionTheory.GKClosure GlobalTheory.CompanionTheory.Hypotheses₂
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.KStable

variable {n : ℕ} {ε : Fin n → Bool}

theorem skew_of_commute {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) :
    Xᴴ = -X := by
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = (Xᴴ * Jm ε) * Jm ε := by rw [Matrix.mul_assoc]
    _ = -(X * (Jm ε * Jm ε)) := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]

theorem exp_mem_Kset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Kset ε := by
  have hs := skew_of_commute hX hc
  have hJ : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv (Formalism.REAL.Jm_mul_self ε)
  have hu : IsUnit (Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hs]
    have hneg : star t • -X = -(t • X) := by simp
    have hcm : Commute (t • X) (-(t • X)) := (Commute.refl _).neg_right
    rw [hneg, ← Matrix.exp_add_of_commute _ _ hcm]
    simp
  · have h1 : Jm ε * (t • X) * (Jm ε)⁻¹ = t • X := by
      rw [hJ, Matrix.mul_smul, Matrix.smul_mul, ← hc, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    have h2 := Matrix.exp_conj (Jm ε) (t • X) hu
    rw [h1, hJ] at h2
    calc NormedSpace.exp (t • X) * Jm ε = Jm ε * NormedSpace.exp (t • X) * Jm ε * Jm ε := by rw [← h2]
      _ = Jm ε * NormedSpace.exp (t • X) := by rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end GlobalTheory.CompanionTheory.Hypotheses₂.KStable

namespace GlobalTheory.CompanionTheory.Hypotheses₂

end GlobalTheory.CompanionTheory.Hypotheses₂

end
