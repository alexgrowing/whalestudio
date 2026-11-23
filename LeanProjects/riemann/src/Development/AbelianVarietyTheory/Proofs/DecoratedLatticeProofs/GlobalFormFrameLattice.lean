import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVectorStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem globalFormAt_frameLat : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DoublingMethod → ∀ D : D7, SiegelWeilFock D → ∀ A : HSp D, GlobalFormAt A (frameLat A) := by
  intro hW hC hDM D hSW A ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hwitt m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1
  have hK := GlobalTheory.T.doublingVector_fockPair_isCompactFinite D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ hΦ₁ hΦ₂
  have hab : A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
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
      rw [← integral_conj]
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
    obtain ⟨hL2, hMG⟩ := GlobalTheory.T.theta_lift_witt_index_vanishing hW hDM D hSW ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt mH hmH Φ hΦ
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

end GlobalTheory.Core.Rk.IP
