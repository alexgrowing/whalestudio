import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SiegelWeilFockAnisotropicUnconditional
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoFree

section
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
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
theorem rallis_inner_product_bottom_norm_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D}
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
  have hG : GlobalFormAniso D := _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
    (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
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
end GlobalTheory.BottomRallis
end
end
