import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.WeilM
open Filter Topology

theorem isLocallyConstant_finprod_evalV {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hy : ∀ᶠ v in Filter.cofinite, ∀ i,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.mono fun v hv => hv
  set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F)} with hT
  have hTfin : T.Finite := hcof.and hy
  have hO : IsOpen {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hU : ∀ᶠ y' in 𝓝 y, ∀ i, ∀ v, (y' i - y i) v ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i :=
      (continuous_apply i).sub continuous_const
    have hmem : (fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i) y ∈
        {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} := by
      intro v
      simp only [sub_self]
      exact zero_mem _
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)
  have hS : ∀ᶠ y' in 𝓝 y, ∀ v ∈ T, (φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) =
      φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
    refine (Filter.eventually_all_finite hTfin).2 fun v _ => ?_
    have hg : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F =>
        fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    exact ((IsLocallyConstant.iff_eventually_eq _).1 ((hφ v).1.comp_continuous hg)) y
  filter_upwards [hU, hS] with y' hU' hS'
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ T
  · exact hS' v hv
  · have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
        ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      simpa [hT] using hv
    obtain ⟨h1, h2⟩ := hv'
    have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) ∈ v.adicCompletionIntegers F := by
      intro i
      have h4 := add_mem (hU' i v) (h2 i)
      have h5 : (y' i - y i) v + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) := by
        show (y' i) v - (y i) v + (y i) v = (y' i) v
        exact sub_add_cancel _ _
      rwa [h5] at h4
    rw [h1, Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3),
      Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
    rfl

end GlobalTheory.WeilM
