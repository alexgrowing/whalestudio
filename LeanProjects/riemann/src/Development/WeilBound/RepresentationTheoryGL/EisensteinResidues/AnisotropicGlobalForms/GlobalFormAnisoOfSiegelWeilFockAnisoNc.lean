import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVectorStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubledStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftWittIndexVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariablesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMemStatement
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConjStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteRightTranslateFiniteAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormFrameLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransferStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchinoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.BottomRallis

open GlobalTheory.Core.Rk.GlobMove

theorem normSq_theta_modGrowth_aniso_nc : GlobalTheory.Published.WeilRepresentationUnitaryPair → ResidueKilled.DM → ∀ D : D7, SiegelWeilFockAniso D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hW hDM D hSW ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt mH hmH Φ hΦ
  obtain ⟨ha, ht, hb, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have hab : A.rank < B.rank := by omega
  have hw : wittIndex B = 0 := hwitt
  obtain ⟨-, -, -, hθ', -, -, hcA, hcB, -⟩ := hP.setting
  have hc := GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A sA a hθ' hcA hP.maj_eq
  have hF := GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ A B sA sB hP.weil.std hθ' Φ Φ hΦ hΦ
  obtain ⟨hint, hEV⟩ := hSW ψ A B ha hab hw χB omh homh a hP.maj θ _ sB hθ' hc.1 hcB hc.2 ν 𝓕 hP.covol mH hmH _ hF

  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hP.weil.om_aut 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hΦ.1)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hP.weil.om_cont Φ hΦ.1 0).comp (Continuous.prodMk_right g)
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩

  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨k, hk⟩ := (hDM D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem).1.2 (sZero A B)
  obtain ⟨r, hr, -, -, C₁, N, hC₁⟩ := GlobalTheory.Eis.EisRegularAt.of_eisValueAt hk hEV
  have hE : ∀ x, ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) x‖ ≤ C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have e := (hEV.2 x).valueAt.cont_eq
    have := hC₁ (sZero A B) (Metric.mem_ball_self hr) x
    rw [GlobalTheory.Eis.eisCont, e] at this
    exact this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (norm_nonneg _).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A

  have hvol := GlobalTheory.RallisIP.Model.vol_pos (B := B) mH
  have hfin : IsFiniteMeasure (autMeasure B mH) := by
    refine ⟨lt_top_iff_ne_top.2 fun h => ?_⟩
    simp [Measure.real, h] at hvol
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ =
      (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖ := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul, ← measure_smul_average, norm_smul, ThetaMean.thetaMean,
      Real.norm_of_nonneg measureReal_nonneg]
  refine ⟨(autMeasure B mH).real Set.univ * C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  rw [hpet g]
  have hg := GlobalTheory.Grow.height_pos A g
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖
      ≤ (autMeasure B mH).real Set.univ * (C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N) :=
        mul_le_mul_of_nonneg_left (hE _) hvol.le
    _ ≤ (autMeasure B mH).real Set.univ * (C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁0) hvol.le
    _ = (autMeasure B mH).real Set.univ * C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

theorem globalFormAnisoAt_frameLat_nc : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → ResidueKilled.DM → ∀ D : D7, SiegelWeilFockAniso D → ∀ A : HSp D, GlobalFormAnisoAt A (frameLat A) := by
  intro hW hC hDM D hSW A ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hwitt m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1
  have hK := GlobalTheory.T.doublingVector_fockPair_isCompactFinite D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ hΦ₁ hΦ₂
  have hab : A.rank < B.rank := by omega
  have hw : wittIndex B = 0 := hwitt
  obtain ⟨-, -, -, hθ', -, -, hcA, hcB, -⟩ := hP.setting
  have hc := GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact D θ A sA a hθ' hcA hP.maj_eq
  have hF := GlobalTheory.T.doublingSeesawTensorMap_polynomial_fock_vector D ψ θ A B sA sB hP.weil.std hθ' Φ₁ Φ₂ hΦ₁ hΦ₂
  obtain ⟨-, hEV⟩ := hSW ψ A B ha hab hw χB omh homh a hP.maj θ _ sB hθ' hc.1 hcB hc.2 ν 𝓕 hP.covol mH hmH _ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ₁ Φ₂) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hDM1, -, hDM3⟩ := hDM D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) hmem

  have hf₁ := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u₁ hu₁
  have hf₂ := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u₂ hu₂
  have rd : ∀ u ∈ A0 θ A cA, GlobalTheory.Grow.RapidDec A u := fun u hu =>
    GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (mem_cuspForms.1 hu).1.1 (mem_cuspForms.1 hu).1.2
  obtain ⟨hBI, -⟩ := hDM3 θ hθ hSig cA hCart m hm _ hf₁ _ hf₂

  have hpt : ∀ s g, flat A a (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B) s (io A (g, 1)) *
      conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) =
      integrand om m ν 𝓕 (frameLat A) a Φ₁ Φ₂ u₁ u₂ s g := by
    intro s g
    have e1 : swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) = wcoef om ν 𝓕 Φ₁ Φ₂ g :=
      (hCC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1).2 g
    have e2 : conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) = rcoef m u₁ u₂ g := by
      simp only [GlobalTheory.Eis.petCoef, rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend]
      rw [← _root_.integral_conj]
      congr 1
      funext q
      simp
    rw [integrand, ← e1, ← e2]
    rfl
  have hZ : ∀ s : ℂ, (A.rank : ℝ) / 2 < s.re →
      Integrable (integrand om m ν 𝓕 (frameLat A) a Φ₁ Φ₂ u₁ u₂ s) m ∧
      GlobalTheory.Eis.zeta A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B))
                   (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) s =
        ∫ g, integrand om m ν 𝓕 (frameLat A) a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
    intro s hs
    obtain ⟨-, hconv, heq⟩ := hBI s hs
    refine ⟨?_, ?_⟩
    · have e : integrand om m ν 𝓕 (frameLat A) a Φ₁ Φ₂ u₁ u₂ s = fun g =>
          flat A a (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B) s (io A (g, 1)) *
            starRingEnd ℂ (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) :=
        funext fun g => (hpt s g).symm
      rw [e]
      exact hconv
    · rw [GlobalTheory.Eis.zeta, heq]
      unfold zetaH pairInt
      exact integral_congr_ae (.of_forall fun g => hpt s g)

  have hEF := hDM1.1.1
  have hZF : GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B))
      (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) := ⟨hEF, fun s hs => (hBI s hs).1⟩
  obtain ⟨-, hZV⟩ := GlobalTheory.T.doubling_zeta_value_at_eisenstein_holomorphic_point D A χB⁻¹ hHk m hm _ hDM1.1 (fun g => hEF.analyticOnNhd_flat g) hDM1.2 _ _
    (rd _ hf₁) (rd _ hf₂) hZF (sZero A B) _ hEV

  have hKer : ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
      Continuous (Function.uncurry fun g h => thetaKO om g h Φ) ∧
      (∀ γ ∈ GQ A, ∀ g h, thetaKO om (γ * g) h Φ = thetaKO om g h Φ) ∧
      (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ) ∧
      ∀ h, GlobalTheory.Grow.ModGrowth A fun g => thetaKO om g h Φ := by
    intro Φ hΦ
    obtain ⟨hL2, hMG⟩ := normSq_theta_modGrowth_aniso_nc hW hDM D hSW ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt mH hmH Φ hΦ
    refine ⟨hP.weil.om_cont Φ hΦ.1 0, fun γ hγ g h => ?_, hL2, hMG, fun h => ?_⟩
    · have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hP.weil.om_aut γ hγ 1 (one_mem _) _ (hP.weil.om_pres _ _ hΦ.1)
    · obtain ⟨C, N, hCN⟩ := GlobalTheory.T.theta_kernel_moderate_growth_both_variables D ψ A B χA χB om hP.weil Φ hΦ.1
      refine ⟨C * GlobalTheory.Grow.height B h ^ N, N, fun g => (hCN g h).trans (le_of_eq ?_)⟩
      rw [mul_pow]; ring
  obtain ⟨i₁, i₂, l₁, l₂, hss⟩ := GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels D A B m mH hm hmH (fun g h => thetaKO om g h Φ₁)
    (fun g h => thetaKO om g h Φ₂) (fun K hK => by
      rcases hK with rfl | rfl
      exacts [hKer Φ₁ hΦ₁, hKer Φ₂ hΦ₂]) u₁ u₂ (rd u₁ hu₁) (rd u₂ hu₂)
  refine ⟨⟨i₁, l₁⟩, ⟨i₂, l₂⟩, fun s hs => (hZ s hs).1,
    GlobalTheory.Eis.dblInt A χB⁻¹ m (ThetaMean.thetaMean omh mH (delta A B Φ₁ Φ₂)) (fun x => conj (u₁ x))
      (fun x => conj (u₂ x)), hZV.2.congr ⟨(A.rank : ℝ) / 2, fun s hs => (hZ s hs).2⟩, ?_⟩

  have key : ∀ g₁ g₂ h, thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) * thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂) := by
    intro g₁ g₂ h
    rw [(hid g₁ g₂ h).2]
    have e : ((χB (detA A g₂) : Circle) : ℂ) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂))) * e
  have hpet : ∀ g₁ g₂, petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) *
        ((volQ B mH : ℂ) * ThetaMean.thetaMean omh mH (delta A B Φ₁ Φ₂) (io A (g₁, g₂))) := by
    intro g₁ g₂
    have e1 : petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
        ((χB (detA A g₂) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂)) q
            ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g₁ g₂ _
    rw [e1, ← measure_smul_average, ThetaMean.thetaMean, Complex.real_smul]
    rfl
  have hss' : petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = _ := hss
  rw [hss', GlobalTheory.Eis.dblInt, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun q => ?_)
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, hpet, MonoidHom.inv_apply, Circle.coe_inv, inv_inv,
    RCLike.conj_conj]
  ring

theorem globalFormAnisoAt_move_nc : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    GlobalFormAnisoAt A L → GlobalFormAnisoAt A L' := by
  intro D A L L' hL hL' hG
  obtain ⟨k, hk, hh⟩ := GlobalTheory.T.doubledLatticeHeight_selfDual_lattices_eq_conj D A L L' hL hL'
  intro ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  haveI := hm
  haveI := hmH
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds A m hm
  have hW := hP.weil
  have hθ : IsInfFam θ := hP.setting.2.2.2.1
  have hki : k⁻¹ ∈ GfC A := inv_mem hk
  have fock : ∀ Φ, IsFockVec ψ θ A B sA sB Φ → IsFockVec ψ θ A B sA sB (om (k⁻¹, 1) Φ) := by
    rintro Φ ⟨hΦ, N, hN⟩
    refine ⟨hW.om_pres _ _ hΦ, N, fun l hl => ?_⟩
    refine GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ A B χA χB om sA sB hW hθ k⁻¹ (fun τ => ?_) N Φ hΦ hN l hl
    rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ A hki τ, Matrix.one_mul, Matrix.mul_one]
  have lu₁ := cuspFormsArchimedeanKFinite_left_invariant hu₁
  have lu₂ := cuspFormsArchimedeanKFinite_left_invariant hu₂

  have upEq : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      (∀ h, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h (om (k⁻¹, 1) Φ) * rTr A k⁻¹ u g) =
        AutomorphicL2Unitary.descend (GQ A) (fun g => (fun x => thetaKO om x h Φ * u x) (g * k⁻¹))) ∧
      ∀ h, AutomorphicL2Unitary.LeftInv (GQ A) (fun x => thetaKO om x h Φ * u x) := by
    intro Φ hΦ u hu
    refine ⟨fun h => ?_, fun h γ hγ g => ?_⟩
    · congr 1
      funext g
      rw [thetaKO_om]
      rfl
    · simp only [leftInv_thetaKO hW hΦ h γ hγ g, hu γ hγ g]
  have upConvIff : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u ∧
      (UpConv om m mH (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) → UpConv om m mH Φ u) := by
    intro Φ hΦ u hu
    obtain ⟨e1, e2⟩ := upEq Φ hΦ u hu
    have hup : up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u := by
      funext h
      simp only [up]
      rw [e1 h, integral_descend_mul_right m (e2 h) k⁻¹]
    refine ⟨hup, fun ⟨c1, c2⟩ => ⟨fun h => ?_, hup ▸ c2⟩⟩
    have := c1 h
    rw [e1 h, integrable_descend_mul_right_iff m (e2 h) k⁻¹] at this
    exact this

  have hint : ∀ s y, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s y =
      integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) := by
    intro s y
    simp only [integrand]
    rw [wcoef_om hW hP.covol hΦ₁.1 hΦ₂.1, rcoef_rTr m lu₁ lu₂, hh a hP.maj]
    congr 3
    group
  obtain ⟨c1, c2, c3, z, hz, hpet⟩ := hG ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH
    (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (fock Φ₁ hΦ₁) (fock Φ₂ hΦ₂)
    (rTr A k⁻¹ u₁) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₁ hu₁)
    (rTr A k⁻¹ u₂) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₂ hu₂)
  obtain ⟨up₁, cv₁⟩ := upConvIff Φ₁ hΦ₁.1 u₁ lu₁
  obtain ⟨up₂, cv₂⟩ := upConvIff Φ₂ hΦ₂.1 u₂ lu₂
  refine ⟨cv₁ c1, cv₂ c2, fun s hs => integrable_of_conj m k ?_, z, ?_, ?_⟩
  · have := c3 s hs
    rwa [show integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s =
      fun y => integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) from funext (hint s)] at this
  · have e : (fun s => ∫ g, integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s g ∂m) =
        fun s => ∫ g, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s g ∂m := by
      funext s
      simp only [hint]
      rw [integral_conj m (integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s) k]
    rw [e]
    exact hz
  · rw [← up₁, ← up₂]
    exact hpet

theorem globalFormAniso_of_siegelWeilFockAniso_nc : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay →
    ResidueKilled.DM → ∀ D : D7, SiegelWeilFockAniso D → GlobalFormAniso D := by
  intro hW hC hDM D hSW A L hL
  exact globalFormAnisoAt_move_nc D A (frameLat A) L (frameLat_isSelfDualC A) hL
    (globalFormAnisoAt_frameLat_nc hW hC hDM D hSW A)

end GlobalTheory.BottomRallis
