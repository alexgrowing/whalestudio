import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoordsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatricesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoeffIsotropicTranslatesEqFourierCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanThetaProductConjEqRestrictionProducStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffAdelicIsotropicPartStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefUnfold

theorem isoPart_add' {D : D7} (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart
  rw [Matrix.add_mul]

private theorem symplOH_eq_zero_of_symplO_eq_zero {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem sum_translates_eq : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ y : Mx D W.rank r, Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖) → ∑' a : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = κ • ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y hs
  have hY' := hY
  obtain ⟨hμH, hYF, hY1⟩ := hY'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI : IsTopologicalAddGroup (Mx D W.rank r) := i1
  haveI : LocallyCompactSpace (Mx D W.rank r) := i2
  haveI : SecondCountableTopology (Mx D W.rank r) := i3
  haveI : T2Space (Mx D W.rank r) := i4
  haveI : DiscreteTopology (ratMx D W.rank r) := i5
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hiso0 : isoPart V W C' (0 : Mx D W.rank r) = 0 := by
    have e := isoPart_add' V W C' (0 : Mx D W.rank r) 0
    rw [add_zero] at e
    have e' : isoPart V W C' (0 : Mx D W.rank r) + isoPart V W C' 0 = isoPart V W C' 0 + 0 := by
      rw [add_zero]; exact e.symm
    exact add_left_cancel e'
  have hpt : ∀ (y' : Mx D W.rank r) (x : WO V' W),
      heisO ψ V W (isoPart V W C y) F (isoPart V W C y' + midPart V V' W B x) =
        F (isoPart V W C (y + y') + midPart V V' W B x) := by
    intro y' x
    have z1 : symplOH V W (isoPart V W C y') (isoPart V W C y) = 0 :=
      symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.1 y' y)
    have z2 : symplOH V W (midPart V V' W B x) (isoPart V W C y) = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.2.1 y x), neg_zero]
    show ψ (symplOH V W (isoPart V W C y' + midPart V V' W B x) (isoPart V W C y)) *
        F (isoPart V W C y' + midPart V V' W B x + isoPart V W C y) = _
    rw [(GlobalTheory.OrientedFormLaws.symplOH_laws D V W).1, z1, z2, add_zero, AddChar.map_zero_eq_one, one_mul,
      isoPart_add']
    congr 1
    abel
  have hP : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 _ _ hF
  let χ : Matrix (Fin W.rank) (Fin r) D.host.E → Mx D W.rank r → ℂ :=
    fun a t => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))
  let Φ : Mx D W.rank r → ℂ := fun t => κ • ∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ
  have hterm : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E,
      (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) =
        ∫ t in 𝓨, χ a t * Φ t ∂μ := fun a =>
    GlobalTheory.T.matrixCoeff_isotropicTranslates_eq_fourierCoeffs D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y a
  obtain ⟨hχc, hχx, hχa, hχΓ, hχ0⟩ := GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices D V V' W r C B hCB C' h1 h2 h3 ψ hψ
  obtain ⟨hΦc, hΦp⟩ := GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hP hG
  have hsum : Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) := by
    have e : (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) =
        fun a => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖ :=
      funext fun a => by rw [hterm a]
    rw [e]
    exact hs
  have key := GlobalTheory.T.fourier_inversion_zero_compact_quotient (Mx D W.rank r) (ratMx D W.rank r) K hK hKc (Matrix (Fin W.rank) (Fin r) D.host.E) χ
    hχc (fun a t s => hχx a t s) (fun a b t => hχa a b t) (fun a t => hψ.1.2.1 _) hχΓ hχ0 μ 𝓨 hμH hYF hY1 Φ
    (hΦc.const_smul κ) (fun γ hγ t => congrArg (fun z : ℂ => κ • z) (hΦp γ hγ t)) hsum
  rw [tsum_congr hterm, ← key]
  show κ • (∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = _
  simp only [hiso0, zero_add]
  simp_rw [hpt]

private theorem symplOH_eq_zero_of_symplO_eq_zero' {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  intro D V V' W r C B hCB ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hCB
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.integral_hom_fundamental_domain_isotropic_split_coords D V V' W r C B hCB C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  have hY' := hY
  obtain ⟨hμH, hYF, -⟩ := hY'
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := hμH
  have hc0 : ENNReal.ofReal κ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hκ0)).ne'
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, MeasureTheory.Measure.IsAddHaarMeasure.smul μ hc0 ENNReal.ofReal_ne_top, ?_⟩
  intro F G hF hG x
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hF₁ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 (midPart V V' W B x) F hF
  have he : ∀ y : Mx D W.rank r, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) =
      heisO ψ V W (isoPart V W C y + midPart V V' W B x) F := by
    intro y
    rw [(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).2.1, symplOH_eq_zero_of_symplO_eq_zero' V W _ _ (hsp.2.1 y x),
      AddChar.map_zero_eq_one, one_smul]
  rw [← ((GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hCB ψ hψ μ 𝓨 hY).1 F hF).2.2.1 x,
    ← GlobalTheory.T.isotropicMean_thetaProduct_conj_eq_restrictionProduct D V V' W r C B hCB ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hF₁ hG]
  simp_rw [← he]
  obtain ⟨hsum, hint⟩ := GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates D W.rank r μ 𝓨 hμH hYF
    (fun y => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) w * star (G w) ∂μV)
    (GlobalTheory.T.integrable_matrixCoeff_adelicIsotropicPart D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ hμH μV 𝓕V hμV hFV _ G hF₁ hG)
  beta_reduce at hsum hint
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 hκ0).le, hint,
    ← MeasureTheory.integral_smul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hsum] with y hy
  rw [sum_translates_eq D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ _ G hF₁ hG y hy,
    smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul]

end GlobalTheory.CoefUnfold

end
