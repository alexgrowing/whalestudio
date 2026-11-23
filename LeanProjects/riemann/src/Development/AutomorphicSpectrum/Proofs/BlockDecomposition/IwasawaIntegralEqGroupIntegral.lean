import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandEqIteratedIntegral
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding.Ptw

theorem main : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ), Φ ∈ LFS.SB F →
  ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ K2 F →
    iw (LFS.Wp ψ W₀ Φ) W' s p = ∫ g, Aq ψ W₀ W' Φ s (p, g) ∂LFS.hG ψ := by
  intro F _ _ _ _ _ _ ψ hψ W₀ W' Φ s hΦ p hp
  have hW := GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.main F ψ hψ W₀ Φ hΦ (hI p)
  have hw : ((wR p : ℝ) : ℂ) = mp p.1 (-1) := by
    rw [wR, mp, Complex.cpow_neg_one]
    push_cast
    rfl
  have hpt : ∀ g : GL (Fin 2) F, Aq ψ W₀ W' Φ s (p, g) =
      (((wR p : ℝ) : ℂ) * mp (GeneralLinearGroup.det (hI p)) s * W' (hI p)) *
        (pFT ψ Φ g.val (e2r (hI p * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * W₀ (hI p * g⁻¹)) := by
    intro g
    have e1 : hI p * g⁻¹ * g = hI p := by group
    have e2 : mp (GeneralLinearGroup.det (hI p * g⁻¹)) s =
        mp (GeneralLinearGroup.det (hI p)) s * mp (GeneralLinearGroup.det g) (-s) := by
      rw [map_mul, map_inv, Iter.mp_mul, Iter.mp_inv]
    have e3 : mp (GeneralLinearGroup.det g) (s + 1 / 2) * mp (GeneralLinearGroup.det g) (-s) =
        mp (GeneralLinearGroup.det g) (1 / 2) := by
      rw [← Iter.mp_add]
      congr 1
      ring
    simp only [Aq, Bq]
    rw [e1, e2]
    linear_combination (((wR p : ℝ) : ℂ) * mp (GeneralLinearGroup.det (hI p)) s * W' (hI p) *
      pFT ψ Φ g.val (e2r (hI p * g⁻¹)) * W₀ (hI p * g⁻¹)) * e3
  have hc : mp (GeneralLinearGroup.det (hI p)) (1 / 2) * mp p.1 (s - 3 / 2) * mp p.2.1 (2 * s - 1) =
      mp p.1 (-1) * mp (GeneralLinearGroup.det (hI p)) s := by
    have ea : mp p.1 (1 / 2) * mp p.1 (s - 3 / 2) = mp p.1 (-1) * mp p.1 s := by
      rw [← Iter.mp_add, ← Iter.mp_add]
      congr 1
      ring
    have eb : mp p.2.1 (2 * (1 / 2)) * mp p.2.1 (2 * s - 1) = mp p.2.1 (2 * s) := by
      rw [← Iter.mp_add]
      congr 1
      ring
    rw [Iter.mp_det_hI p hp, Iter.mp_det_hI p hp]
    linear_combination (mp p.2.1 (2 * (1 / 2)) * mp p.2.1 (2 * s - 1)) * ea +
      (mp p.1 (-1) * mp p.1 s) * eb
  have hiw : iw (LFS.Wp ψ W₀ Φ) W' s p =
      LFS.Wp ψ W₀ Φ (em (hI p)) * W' (hI p) * mp p.1 (s - 3 / 2) * mp p.2.1 (2 * s - 1) := rfl
  simp only [hpt]
  rw [integral_const_mul, hiw, hW, hw]
  linear_combination ((∫ g, pFT ψ Φ g.val (e2r (hI p * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) *
    W₀ (hI p * g⁻¹) ∂LFS.hG ψ) * W' (hI p)) * hc

end GlobalTheory.CompanionTheory.GL2Unfolding.Ptw
