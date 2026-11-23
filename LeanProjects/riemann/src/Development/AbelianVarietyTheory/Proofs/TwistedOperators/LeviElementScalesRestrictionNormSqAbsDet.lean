import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelParsevalThetaInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomainsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionIsotropicPartHomOfFrameMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariablesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

theorem heisO_isoPart_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C' : Matrix (Fin V.rank) (Fin r) D.host.E) (F : WO V W → ℂ) :
    heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0) F = F := by
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0 = 0 := Matrix.zero_mul _
  funext w
  rw [h0]
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

set_option maxHeartbeats 1000000 in

theorem norm_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' a g' m hC _hB h f hf
  have hstd : IsStdChar D ψ (-1) := hω.std
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  obtain ⟨μ₀, 𝓕₀, h0⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  obtain ⟨μ'', 𝓕'', h''⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hstd μ 𝓨 hμ
  have hΩf : IsThetaFunO ψ V W (ω (m, h) f) := hω.om_pres _ f hf
  have pΩ := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ _ hΩf hΩf
  have pf := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f f hf hf
  obtain ⟨N₁, hN₁⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' (ω (m, h) f) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' f := ⟨_, rfl⟩
  have hN₁c : Continuous N₁ := by rw [hN₁]; exact pΩ.1
  have hN₁i : Integrable N₁ μ := by rw [hN₁]; exact pΩ.2.1
  have hN₀c : Continuous N₀ := by rw [hN₀]; exact pf.1
  have hN₀i : Integrable N₀ μ := by rw [hN₀]; exact pf.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank :=
    ⟨_, rfl⟩
  have hcov := GlobalTheory.T.integral_levi_phase_change_of_variables D ψ hstd W r μ hμ.1 h (GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one D W h) a N₀ hN₀c hN₀i
  have hph : ∀ y u : Mx D W.rank r, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) +
      symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) = phase ψ W y u :=
    fun y u => by rw [phase_apply, GlobalTheory.T.symplecticHalf_isotropicParts_add_self_eq_trace D V W r C C' h1 u y]
  rw [← hk] at hcov
  have hφ : Continuous fun u : Mx D W.rank r => (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val : Mx D W.rank r) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : Mx D W.rank r → ℂ,
      N₂ = fun u : Mx D W.rank r => k * N₀ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) := ⟨_, rfl⟩
  have hN₂c : Continuous N₂ := by rw [hN₂]; exact continuous_const.mul (hN₀c.comp hφ)
  have hN₂i : Integrable N₂ μ := by rw [hN₂]; exact hcov.1.const_mul k
  have key : N₁ = N₂ := GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq D ψ hstd W r μ hμ.1 N₁ N₂ hN₁c hN₂c hN₁i hN₂i (fun y => by
    have s1 := GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ hΩf y
    have hz : HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y)
        (GlobalTheory.MixModel.adj (a⁻¹).val))) (GlobalTheory.MixModel.adj a.val) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one, Matrix.mul_one]
    have s2 := GlobalTheory.T.weilDatum_transports_heisenbergMatrixCoeffs D V W ψ χS χT ω hω m h f hf μ₀ 𝓕₀ h0.1 h0.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)))
    rw [GlobalTheory.T.weilAction_isotropicPartHom_of_frameMul D V W r C a m hC h, hz] at s2
    have s3 := GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f hf
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
    simp only [hph] at s1 s3
    rw [← hN₁] at s1
    rw [← hN₀] at s3
    rw [← s1, s2, s3, hcov.2 y, hN₂, ← integral_const_mul]
    congr 1
    funext u
    ring)
  have e0 := congrFun key 0
  rw [hN₁, hN₂, hN₀] at e0
  simp only [resNorm, Matrix.mul_zero, Matrix.zero_mul, heisO_isoPart_zero] at e0
  obtain ⟨p1, fin1, eq1⟩ := GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 _ hΩf).2.1
  obtain ⟨p2, fin2, eq2⟩ := GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 f hf).2.1
  rw [eq1, eq2, hk] at e0
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains D V' W μ' 𝓕' hμ' h𝓕' μ'' 𝓕'' h''
  rw [hc _ (hres.1 _ hΩf).2.1.cont p1, hc _ (hres.1 f hf).2.1.cont p2]
  have eR : (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'').toReal =
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ)) ^ W.rank *
        (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'').toReal := by
    exact_mod_cast e0
  have eE : ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'' =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank *
        ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'' := by
    rw [← ENNReal.toReal_eq_toReal_iff' fin1 (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) fin2),
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
    exact eR
  rw [eE, mul_left_comm]

end GlobalTheory.LeviNorm

end
