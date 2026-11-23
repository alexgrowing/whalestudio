import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFamilyZetaConvergenceHolomorphyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropicGlobalFormOfDoublingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeLStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem siegelWeilFockAniso_of_siegelWeilAnisotropic (hSW : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : D7) :
    SiegelWeilFockAniso D := by
  intro ψ A B ha hab hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hK := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hBc (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hB' : IsAniso B := wittIndex_eq_zero_iff_isAniso.1 hB
  obtain ⟨hint, hv⟩ := hSW D ψ A B ha (ha.trans hab.le) hB' χB omh homh a hmaj hI ν 𝓕 hcov mH hmH φ hF.1 hK
  rw [if_pos hab, one_smul] at hv
  exact ⟨hint, hv⟩

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem heckeFormAniso_of_global_euler (D : D7) (hG : GlobalFormAniso D) (hE : EulerRight D) : HeckeFormAniso D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hw LA LB Sf Φ₁ Φ₂ hF₁ hF₂ hU m mH hm hmH u₁ hu₁ u₂ hu₂ par hpar
    hsph hs
  obtain ⟨s₁, hs₁, hint⟩ := hs
  obtain ⟨hUp₁, hUp₂, hZint, z, hz, hpet⟩ :=
    hG A LA hU.sdA ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hF₁ hF₂ u₁ hu₁ u₂ hu₂
  obtain ⟨hA1, ht1, hB, -⟩ := hP.setting
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero, hB]; push_cast; ring
  have hs0re : (sZero A B).re = (t : ℝ) / 2 := by rw [hs0]; simp
  obtain ⟨hcont, hbd, -⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D A LA a hU.sdA hP.maj
  have hflat : ∀ s, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
        (fun g => (hgtL A LA a g : ℝ)) (sZero A B) s := by
    intro s; funext g
    simp only [integrand, GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand, npow]; ring
  have hmeas : Measurable (fun g => (hgtL A LA a g : ℝ)) := (NNReal.continuous_coe.comp hcont).measurable
  have hfz := GlobalTheory.T.flatFamilyZeta_convergence_holomorphy (GA D A) (m.restrict (openOff A LA Sf)) (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
    (fun g => (hgtL A LA a g : ℝ)) (sZero A B) (s₁ : ℂ) hmeas (fun g => by exact_mod_cast (hbd g).1)
    (fun g => by exact_mod_cast (hbd g).2) (by rw [← hflat]; exact hint)
  have hint0 : IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m := by
    have := hfz.1.1 (sZero A B) (by simp only [Set.mem_setOf_eq, Complex.ofReal_re, hs0re]; linarith)
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self] at this
  refine ⟨hUp₁, hUp₂, hint0, fun l hl => ?_⟩
  have hd := GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank
  have hER : EqRight (fun s => ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (fun s => LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) := by
    refine ⟨(A.rank : ℝ) + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    refine hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hF₁.1 hF₂.1 hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs'
      (hZint s ?_)
    have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    linarith
  have hY : DifferentiableOn ℂ (fun s => ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (rightOf s₁) := by
    have h2 := hfz.2.1
    simp only [Complex.ofReal_re] at h2
    refine h2.congr fun s _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta, hflat]
  have hL : HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) (sZero A B) l := by rw [hs0]; exact hl
  have hmain := GlobalTheory.T.holomorphicContinuationValue_eq_div_mul _ _ _ _ (sZero A B) z l s₁ (by rw [hs0re]; positivity) (by rw [hs0re]; exact hs₁)
    hd.1 (fun s hs => (hd.2 s hs).1) hY hER hz hL
  rw [hpet, hmain, ← hs0]
  simp only [integrand_sZero]
  ring

theorem rcoef_one {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    rcoef m (fun _ : GA D A => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend, volQ]

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem norm_eq (hP : GlobalTheory.FunPr.Hypotheses₂) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D}
    {χA χB : (AE D)ˣ →* Circle} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A} {a : GL (Fin A.rank) (AE D)}
    {om : WRep A B} {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hPair : Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕)
    (hA : wittIndex A = 0) (hB : wittIndex B = 0) {LA : Lat A} {LB : Lat B} {Sf : Finset (FinPl D)}
    {Φ : WO A B → ℂ} (hF : IsFockVec ψ θ A B sA sB Φ) (hU : Unram ψ A B χB LA LB Sf Φ Φ)
    (m : Measure (GA D A)) (mH : Measure (GA D B)) [m.IsHaarMeasure] [mH.IsHaarMeasure]
    (hint : ∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧
      IntegrableOn (integrand om m ν 𝓕 LA a Φ Φ (fun _ => 1) (fun _ => 1) s₁) (openOff A LA Sf) m)
    (l : ℕ → ℂ) (hl : ∀ i < A.rank,
      HolValueAt (LFun.charL χB⁻¹ (Sf : Set (FinPl D))) ((t : ℂ) / 2 + (A.rank : ℂ) / 2 - i) (l i)) :
    petersson B mH (up om m Φ (fun _ => 1)) (up om m Φ (fun _ => 1)) =
      volQ B mH * volQ A m * ((∏ i ∈ Finset.range A.rank, l i) /
        LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
        ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ Φ g ∂m := by
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalFormAniso D := GlobalTheory.T.siegelWeil_anisotropic_global_form_of_doubling hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
    (siegelWeilFockAniso_of_siegelWeilAnisotropic hP.siegelWeilAnisotropicUnitary D)
  have hH := heckeFormAniso_of_global_euler D hG hE
  have h1 : (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero hPair.setting hA
  have hpar := GlobalTheory.T.constantFunction_has_trivialRep_satakeParameters A LA Sf hU.sdA hU.two
  have hsph : SphFun A LA Sf (fun _ : GA D A => (1 : ℂ)) := fun _ _ _ _ _ => rfl
  obtain ⟨-, -, -, hfin⟩ := hH ψ θ A B χA χB sA sB t cA a om ν 𝓕 hPair hB LA LB Sf Φ Φ hF hF hU m mH
    inferInstance inferInstance _ h1 _ h1 (trivPar A.rank) hpar hsph hint
  have hL : HolValueAt (fun s => LFun.LSD D Sf (trivPar A.rank) χB (s + 1 / 2)) ((t : ℂ) / 2)
      (∏ i ∈ Finset.range A.rank, l i) := by
    refine HolValueAt.congr (holValueAt_prod (Finset.range A.rank) fun i hi => ?_) (GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L χB Sf A.rank hU.unr)
    have h2 := hl i (Finset.mem_range.1 hi)
    rw [show (t : ℂ) / 2 + (A.rank : ℂ) / 2 - i = (t : ℂ) / 2 + ((A.rank : ℂ) / 2 - i) by ring] at h2
    have h3 := h2.comp_add
    simpa only [add_sub_assoc] using h3
  rw [hfin _ hL]
  simp only [rcoef_one]
  rw [integral_mul_const]
  ring

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

theorem prod_range_sub_eq_prod_Icc (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

end GlobalTheory.BottomRallis
