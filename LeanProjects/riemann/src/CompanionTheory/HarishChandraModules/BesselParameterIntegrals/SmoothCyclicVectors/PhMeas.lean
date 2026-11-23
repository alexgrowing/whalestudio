import Mathlib
import Formalism.PeriodIntegrals.PhMeasCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

open Matrix Filter Topology Set

noncomputable section

namespace CompanionTheory.D.Upq.Sm

open PI.PhMeasCore

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem ex_mem_of_lie {Hm X : Mat n} (hX : Xᴴ * Hm + Hm * X = 0) (t : ℝ) :
    (ex X t)ᴴ * Hm * ex X t = Hm := by
  refine CCRuleCW.exp_mem_UH Hm _ ?_
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem repOn_of_conj {J Hm P : Mat n} {σ : Mat n → (H →L[ℂ] H)} (hP : IsUnit P)
    (hPJ : Pᴴ * J * P = Hm) (h1 : σ (P⁻¹ * 1 * P) = 1)
    (hm : ∀ a, aᴴ * J * a = J → ∀ b, bᴴ * J * b = J →
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) :
    RepOn {g | gᴴ * Hm * g = Hm} σ := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp hP
  have e1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
  have hc : ∀ a : Mat n, P⁻¹ * (P * a * P⁻¹) * P = a := fun a => by
    rw [show P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      e1, Matrix.one_mul, Matrix.mul_one]
  have hJ : ∀ a : Mat n, aᴴ * Hm * a = Hm → (P * a * P⁻¹)ᴴ * J * (P * a * P⁻¹) = J := by
    intro a ha
    calc (P * a * P⁻¹)ᴴ * J * (P * a * P⁻¹) = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * J * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * J * (P * P⁻¹) := by
          rw [hPJ, ha, ← hPJ]; simp only [Matrix.mul_assoc]
      _ = J := by rw [e3, e2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨by simp, fun a ha b hb => CCRuleCW.UH_mul Hm a b ha hb, ?_, fun a ha b hb => ?_⟩
  · rwa [Matrix.mul_one, e1] at h1
  · have := hm _ (hJ a ha) _ (hJ b hb)
    rw [hc, hc] at this
    rw [← this]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], e1]
    simp

end CompanionTheory.D.Upq.Sm

end
