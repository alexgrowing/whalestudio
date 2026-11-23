import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIntegrandIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableTinvIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerInducedOfFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierWeylTransposeInverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftRightPartialFourierIntegralEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftPartialFourierTwistedIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightPartialFourierTwistedIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzBruhatMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRightPartialFourierStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightPartialFourierSupportBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSupportCompactBoundedEntriesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerIntegralEqLeftPartialFourierStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusDetLongWeylBlockStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualChangeOfVariablesIdentitiesStatement
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair

theorem mp_inv' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F]
    (a : Fˣ) (s : ℂ) : mp a⁻¹ s = mp a (-s) := by
  have h1 : mp a⁻¹ s * mp a s = 1 := by
    rw [← KTwoWhittakerSubgroup.mp_mul]
    simp [mp]
  have h2 : mp a (-s) * mp a s = 1 := by
    rw [← KTwoWhittakerSubgroup.mp_add]
    simp [mp]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)

theorem det_unipotent_adele {F : Type} [Field F] (u : F) : GeneralLinearGroup.det (uni2 u) = 1 := by
  ext
  simp [GeneralLinearGroup.val_det_apply, uni2, Matrix.det_fin_two]

theorem unipotent_inv_eq_neg {F : Type} [Field F] (u : F) : (uni2 u)⁻¹ = uni2 (-u) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_neg_identity_GL2 {F : Type} [Field F] : GeneralLinearGroup.det (dg2 (-1 : Fˣ) (-1)) = 1 := by
  ext
  simp [GeneralLinearGroup.val_det_apply, dg2, Matrix.det_fin_two]

theorem main : Ad3.K.GL2LocalData.GodementSectionDual := by
  intro F _ _ _ _ _ _ ψ hψ ν hν0 W₀ hW₀ Φ hΦ₀ h
  have hyp : LFS.Hyp ψ ν W₀ Φ :=
    ⟨hψ, hν0, ⟨V2 ψ ν ν⁻¹, GlobalTheory.CompanionTheory.WhittakerInducedSpan.whittaker_induced_space GlobalTheory.CompanionTheory.WhitFE.feGen F ψ hψ ν ν⁻¹ hν0 (GlobalTheory.CompanionTheory.LocalChar.sInv F ν hν0).1, hW₀⟩, hΦ₀⟩
  haveI hμ : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  haveI hRi : (LFS.hG ψ).IsMulRightInvariant := by unfold LFS.hG; infer_instance
  haveI hinv : (LFS.hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (LFS.hG ψ)⟩
  obtain ⟨-, hν, ⟨V', H, hW⟩, hΦ⟩ := id hyp
  set A : GL (Fin 2) F → ℂ := fun z => W₀ z * mp (GeneralLinearGroup.det z) (-(3 / 2)) with hA
  set g3 : GL (Fin 3) F := w3 * tinv (em h) with hg3
  have hLpt : ∀ y : GL (Fin 2) F, W₀ y⁻¹⁻¹ * mp (GeneralLinearGroup.det y⁻¹) (3 / 2) * LFS.inn ψ Φ y⁻¹ g3 =
      A y * Lpart ψ (Pf Φ h y) := by
    intro y
    rw [inv_inv, map_inv, mp_inv', hg3, GlobalTheory.T.inner_integral_eq_left_partial_fourier F ψ Φ y h]
  have hLint : Integrable (fun z => A z * Lpart ψ (Pf Φ h z)) (LFS.hG ψ) := by
    have h0 := (GlobalTheory.CompanionTheory.LFAbs.integrable_wPhi F ψ ν W₀ Φ hyp g3).comp_inv
    exact h0.congr (Filter.Eventually.of_forall hLpt)
  have hL : dW3 (LFS.Wp ψ W₀ Φ) (em h) =
      mp (GeneralLinearGroup.det h) (-1) * ∫ z, A z * Lpart ψ (Pf Φ h z) ∂LFS.hG ψ := by
    change LFS.Wp ψ W₀ Φ g3 = _
    unfold LFS.Wp
    rw [hg3, GlobalTheory.T.modulus_det_long_weyl_block F h, ← hg3]
    congr 1
    rw [← integral_inv_eq_self (fun k => W₀ k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * LFS.inn ψ Φ k g3)]
    exact integral_congr_ae (Filter.Eventually.of_forall hLpt)
  set f : GL (Fin 2) F → ℂ := fun g =>
    dFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * dW2 W₀ (h * g⁻¹) with hf
  have hsub : ∫ g, f g ∂LFS.hG ψ = ∫ z, f (tinv z⁻¹ * w2 * h) ∂LFS.hG ψ := by
    have e1' := integral_mul_right_eq_self (μ := LFS.hG ψ) f (w2 * h)
    have e2' := GlobalTheory.CompanionTheory.GL2LocalData.HaarTinv.integral_tinv ψ (fun u => f (u * (w2 * h)))
    have e3' := integral_inv_eq_self (fun z => f (tinv z * (w2 * h))) (LFS.hG ψ)
    rw [← e1', ← e2', ← e3']
    simp only [mul_assoc]
  have hcen : ∀ z, W₀ (dg2 (-1) (-1) * z) = W₀ z := by
    intro z
    rw [H.cen W₀ hW]
    simp
  have hdet : ∀ (z : GL (Fin 2) F) (s : ℂ),
      mp (GeneralLinearGroup.det (dg2 (-1) (-1) * z)) s = mp (GeneralLinearGroup.det z) s := by
    intro z s
    rw [map_mul, det_neg_identity_GL2, one_mul]
  have hpt : ∀ z : GL (Fin 2) F, f (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h) =
      (mp (GeneralLinearGroup.det h) (1 / 2) * mp (GeneralLinearGroup.det h) (-2)) *
        (A z * Rpart ψ (Pf Φ h z)) := by
    intro z
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.dual_change_of_variables_identities F W₀ h (dg2 (-1) (-1) * z) (1 / 2)
    simp only [hf, hA]
    rw [a1, a2, a3, GlobalTheory.T.partial_fourier_weyl_transpose_inverse F ψ hψ, hcen, hdet]
    have hz : mp (GeneralLinearGroup.det z) (-(3 / 2)) =
        mp (GeneralLinearGroup.det z) (-2) * mp (GeneralLinearGroup.det z) (1 / 2) := by
      rw [← KTwoWhittakerSubgroup.mp_add]
      norm_num
    rw [hz]
    ring
  have hR : ∫ g, f g ∂LFS.hG ψ = (mp (GeneralLinearGroup.det h) (1 / 2) * mp (GeneralLinearGroup.det h) (-2)) *
      ∫ z, A z * Rpart ψ (Pf Φ h z) ∂LFS.hG ψ := by
    rw [hsub, ← integral_mul_left_eq_self (fun z => f (tinv z⁻¹ * w2 * h)) (dg2 (-1) (-1))]
    simp only [hpt]
    rw [integral_const_mul]
  have hAc : Continuous A := by
    obtain ⟨U, hU⟩ := H.smooth W₀ hW
    have hWc : Continuous W₀ :=
      (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant W₀ U.toSubgroup U.isOpen hU).continuous
    exact hWc.mul (GlobalTheory.CompanionTheory.LFHolP.continuous_mp_det _)
  have hRint : Integrable (fun z => A z * Rpart ψ (Pf Φ h z)) (LFS.hG ψ) := by
    obtain ⟨R, hRs⟩ := GlobalTheory.T.right_partial_fourier_support_bounded F ψ hψ Φ hΦ h
    obtain ⟨C, hC, hCs⟩ := GlobalTheory.T.whittaker_support_compact_bounded_entries F ψ hψ ν V' H W₀ hW R
    refine (hAc.mul (GlobalTheory.T.continuous_right_partial_fourier F ψ hψ Φ hΦ h)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hC fun z hz => ?_)
    have hz' : A z * Rpart ψ (Pf Φ h z) ≠ 0 := hz
    have hr := right_ne_zero_of_mul hz'
    have hw : W₀ z ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hz')
    exact hCs z hw (hRs z hr).1 (hRs z hr).2
  have hcore := GlobalTheory.T.left_right_partial_fourier_integral_eq F ψ hψ
    (fun p hp => (GlobalTheory.T.left_partial_fourier_twisted_integral F ψ hψ p hp).trans (GlobalTheory.T.right_partial_fourier_twisted_integral F ψ hψ p hp).symm)
    A (fun z => Pf Φ h z)
    (fun u z => by
      simp only [hA]
      rw [H.psi W₀ hW, map_mul, det_unipotent_adele, one_mul, mul_assoc])
    (fun u z M => by
      simp only [Pf]
      rw [_root_.mul_inv_rev, unipotent_inv_eq_neg, Units.val_mul, Matrix.mul_assoc _ _ M]
      congr 2
      rw [← Matrix.mulVec_mulVec]
      congr 1
      ext i
      fin_cases i <;> simp [uni2, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
    (fun z => GlobalTheory.T.pullback_schwartz_bruhat_matrix F Φ hΦ h z) hLint hRint
  change dW3 (LFS.Wp ψ W₀ Φ) (em h) = _ * ∫ g, f g ∂LFS.hG ψ
  rw [hL, hR, hcore, ← mul_assoc, ← mul_assoc, ← KTwoWhittakerSubgroup.mp_add, ← KTwoWhittakerSubgroup.mp_add]
  norm_num

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair
