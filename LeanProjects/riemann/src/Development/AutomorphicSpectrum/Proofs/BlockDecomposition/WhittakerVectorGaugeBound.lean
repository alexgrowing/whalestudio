import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTemperedBoundDetOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableGodementJacquetDual
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhIwasawa

theorem continuous_and_iwasawa_bound : ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', Continuous W ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : GL (Fin 2) F,
  ‖W h‖ ≤ C * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε) := by
  intro F _ _ _ _ _ _ ψ hψ ω G V' hω H W hW
  refine ⟨?_, fun ε hε => ?_⟩
  · obtain ⟨U, hU⟩ := H.smooth W hW
    exact GlobalTheory.CompanionTheory.GJMeas.continuous_of_rightInvariant W U hU
  · obtain ⟨C, B, hC, hCB⟩ := GlobalTheory.CompanionTheory.GJTwo.WhB.whittaker_bound_det_one F ψ hψ ω G V' hω H W hW ε hε
    refine ⟨C, hC, fun h => ?_⟩
    have hy : ((GeneralLinearGroup.det h : Fˣ) : F) = (h.val).det := rfl
    have hy0 : (h.val).det ≠ 0 := by
      rw [← hy]
      exact Units.ne_zero _
    have hg : ((dg2 (GeneralLinearGroup.det h)⁻¹ 1 * h : GL (Fin 2) F).val).det = 1 := by
      have hd : ((dg2 (GeneralLinearGroup.det h)⁻¹ 1 : GL (Fin 2) F).val).det = ((h.val).det)⁻¹ := by
        simp [dg2, Matrix.det_fin_two, hy]
      rw [Units.val_mul, Matrix.det_mul, hd, inv_mul_cancel₀ hy0]
    have hrow : (fun j => (dg2 (GeneralLinearGroup.det h)⁻¹ 1 * h : GL (Fin 2) F).val 1 j) = e2r h := by
      funext j
      fin_cases j <;> simp [dg2, e2r, Matrix.mul_apply, Fin.sum_univ_two]
    have hyg : dg2 (GeneralLinearGroup.det h) 1 * (dg2 (GeneralLinearGroup.det h)⁻¹ 1 * h) = h := by
      rw [← mul_assoc]
      have : (dg2 (GeneralLinearGroup.det h) 1 * dg2 (GeneralLinearGroup.det h)⁻¹ 1 : GL (Fin 2) F) = 1 := by
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, hy, hy0]
      rw [this, one_mul]
    have key := (hCB (GeneralLinearGroup.det h) _ hg).1
    rw [hyg, hrow, hy] at key
    exact key

end GlobalTheory.CompanionTheory.WhIwasawa
