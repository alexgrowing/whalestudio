import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval

open Ad3 Ad3.LR Ad3.LR.C

lemma of_mul_blk (h : M22) (z : Fin 2 → ℝ) :
    Matrix.of.symm (Matrix.of h * blk z) = cat h (fun r => h r 0 * z 0 + h r 1 * z 1) := by
  funext r c
  fin_cases c <;> simp [cat, blk, Matrix.mul_apply, Fin.sum_univ_succ]

lemma dualF_pair (h : M22) (ζ : ℝ) (z : Fin 2 → ℝ) (hd : (Matrix.of h).det ≠ 0) :
    ζ * z 0 + z 1 = dualF h ζ 0 * (h 0 0 * z 0 + h 0 1 * z 1) +
      dualF h ζ 1 * (h 1 0 * z 0 + h 1 1 * z 1) := by
  have hD : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    simp [Matrix.det_fin_two]
  simp only [dualF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  rw [hD]
  ring

theorem gz_eq_fz : ∀ (Φ : Ad3.LR.Sw) (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    GlobalTheory.CompanionTheory.Parseval.gz Φ h ζ = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) *
      GlobalTheory.CompanionTheory.Parseval.fz Φ h (GlobalTheory.CompanionTheory.Parseval.dualF h ζ) := by
  intro Φ h ζ hd
  let L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (Matrix.of h)
  have hLdet : LinearMap.det L = (Matrix.of h).det := LinearMap.det_toLin' _
  have hLz : ∀ z, L z = fun r => h r 0 * z 0 + h r 1 * z 1 := by
    intro z
    funext r
    simp [L, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  let G : (Fin 2 → ℝ) → ℂ := fun y => Φ (cat h y) *
    Complex.exp (2 * Real.pi * Complex.I * ((dualF h ζ 0 * y 0 + dualF h ζ 1 * y 1 : ℝ) : ℂ))
  have hcat : Continuous (fun y : Fin 2 → ℝ => cat h y) := by
    refine continuous_pi fun r => continuous_pi fun c => ?_
    fin_cases c
    · simpa [cat] using continuous_const
    · simpa [cat] using continuous_const
    · simpa [cat] using continuous_apply r
  have hG : Continuous G := by
    refine (Φ.continuous.comp hcat).mul (Complex.continuous_exp.comp ?_)
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    fun_prop
  have hmap : Measure.map L (volume : Measure (Fin 2 → ℝ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hLdet]; exact hd)
  have hint : ∫ z, G (L z) = ∫ y, G y ∂(Measure.map L volume) :=
    (integral_map L.continuous_of_finiteDimensional.aemeasurable hG.aestronglyMeasurable).symm
  have hgz : gz Φ h ζ = ∫ z, G (L z) := by
    unfold gz
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [G]
    rw [of_mul_blk, hLz, dualF_pair h ζ z hd]
  rw [hgz, hint, hmap, integral_smul_measure, hLdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp [fz, G, Complex.real_smul]

end GlobalTheory.CompanionTheory.Parseval
