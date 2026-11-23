import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalCompatibilityHolds
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationSymmetry
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.AboveL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasCohomologyTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRepOfIsAssoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIsConjAndLocComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Wigner
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.ContraPair
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Lit.Car

private theorem regAlg_of_coh (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (π : CuspSub E a) (hπ : GlobalTheory.GKCoh.IsCohomological π) : (CG.mk π).IsRegAlg := by
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  obtain ⟨Ξ, hΞ⟩ := hπ
  choose m' h1 h2 h3 using fun σ => GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ σ
  have e : (fun σ => (CG.mk π).infChar σ) = m' := by
    by_contra hne
    exact UpperTheory.V.AlgRepEndIrreducible.wigner E a π Ξ _ m' (fun σ => GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) σ) h1 hne hΞ
  rw [show (CG.mk π).infChar τ = m' τ from congrFun e τ]
  exact ⟨h2 τ, h3 τ⟩

private theorem mem_of_induces {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) :
    ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  rw [← h, hj.valuation_lt_one_iff]
  have : Bw.j (algebraMap F Ω (((l : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [this, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem triv_of_abW {y : WD h} (hy : UpperTheory.V.Lev.AbW y) : ∀ g ∈ ⁅(⊤ : Subgroup ↥(Weil h)), (⊤ : Subgroup ↥(Weil h))⁆, LocalGlobalAboveLAlt.Triv y g := by
  induction y using WD.ind with
  | hP n a =>
    intro g hg
    rw [GlobalTheory.CompanionTheory.RelSym.triv_mk_iff]
    have : ⁅(⊤ : Subgroup ↥(Weil h)), (⊤ : Subgroup ↥(Weil h))⁆ ≤ a.ρ.ker := Subgroup.commutator_le.2 fun s _ t _ =>
      (GlobalTheory.CompanionTheory.RelSym.triv_mk_iff a _).1 (hy s t)
    exact this hg

theorem ssCmp_of_rel {x y : WD h} (r : LocalGlobalAboveLAlt.Rel x y) : UpperTheory.V.Lev.SsCmp x y := by
  rintro (hx | hy) s
  · exact ((LocalGlobalAboveLAlt.relSymm E Ω A w h x y r).2.2 ⊤ .top (triv_of_abW hx) s trivial).symm
  · exact r.2.2 ⊤ .top (triv_of_abW hy) s trivial
end

theorem lg_of (h1 : LocalGlobalAboveLAlt.LocalGlobalSubnormal) (h2 : LocalGlobalAboveLAlt.TemperednessTransfer) : LG :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w hw A h O _ _ _ Bw hj σ hσ rc hrc =>
    have k := h1 E Ω l ι a ha π hc hr r wt HT hG P AI hT w hw A h O Bw hj σ hσ rc hrc
    ⟨k.1, k.2.1.2, LocalGlobalAboveLAlt.relIneAb E Ω A w h _ _ k, fun _ => h2 E Ω l ι a ha π hc hr r wt HT hG P AI hT w hw A h O Bw hj σ hσ rc hrc⟩

theorem csdSs_of (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable) (h1 : LocalGlobalAboveLAlt.LocalGlobalSubnormal) :
    UpperTheory.V.Lev.CsdSs := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hd hcoh
  have hreg := regAlg_of_coh E a π hcoh
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired hF E a π (hGK E a π) hd
  obtain ⟨r, wt, HT, hr⟩ := hG.of_isCsd Ω ι (by omega) hreg hc
  refine ⟨r, hr.cont, hr.ss, hr.away, fun P AI hT w A h O _ _ _ Bw hj => ⟨hT.elim fun T => hr.isPstAt hB T h Bw hj, fun σ hσ rc hrc => ?_⟩⟩
  exact ssCmp_of_rel (h1 E Ω l ι a ha π hc hreg r wt HT hr P AI hT w (mem_of_induces h Bw hj) A h O Bw hj σ hσ rc hrc)

theorem dualR_of (hC : UpperTheory.CBC.LitCBC2) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  have hG := (bridge' hGK).2 hP
  have hW := PositivityTheory.Pf1.CLGD.K.kKW hC
  ⟨lg_of (LocalGlobalAboveLAlt.local_global_compatibility_holds hW hG hB hL hJ) (LocalGlobalAboveLAlt.temperedness_transfer_holds hW hG hB hL hJ),
    csdSs_of hF hGK hG hB (LocalGlobalAboveLAlt.local_global_compatibility_holds hW hG hB hL hJ)⟩

theorem csdSs_of_lit (hC : UpperTheory.CBC.LitCBC2) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : UpperTheory.V.Lev.CsdSs := (dualR_of hC hF hGK hP hB hL hJ).2

end UpperTheory.Lit.Car

end
