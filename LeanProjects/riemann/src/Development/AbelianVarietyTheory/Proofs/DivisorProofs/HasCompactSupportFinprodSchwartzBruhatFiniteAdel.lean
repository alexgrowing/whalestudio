import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
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

namespace GlobalTheory.AdelicCoordSupport

theorem hasCompactSupport_finprod : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ φ hSB hae
  classical
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → Fv F v) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  have hLc : ∀ v, IsClosed (L v) := fun v => by
    have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [L]
    rw [e]
    exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ L v := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  have hfac : ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      (∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 →
      ∀ v, φ v (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 := by
    intro y h v
    have hfin : (Function.mulSupport fun v => φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)).Finite := by
      refine (Filter.eventually_cofinite.1 (hae.and (hint y))).subset ?_
      intro w hw h'
      apply hw
      simp only
      rw [h'.1, Set.indicator_of_mem h'.2]
      rfl
    rw [finprod_eq_prod _ hfin] at h
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.prod_ne_zero_iff.1 h v hv
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      rw [hv]
      exact one_ne_zero
  let D : κ → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun i v =>
    ((fun Z : κ → Fv F v => Z i) '' tsupport (φ v)) ∪ (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i v, IsCompact (D i v) := fun i v =>
    ((hSB v).2.isCompact.image (continuous_apply i)).union (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i, ∀ᶠ v in Filter.cofinite,
      D i v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (φ v) ⊆ L v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (hLc v)
    exact hsub hZ i
  let Box : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
    Set.pi Set.univ fun i => {x | ∀ v, x v ∈ D i v}
  have hbox : IsCompact Box :=
    isCompact_univ_pi fun i => PI.VolStabS.AdmissibleCompactSupport.isCompact_finBox (hD i) (hDe i)
  refine HasCompactSupport.intro hbox fun y hy => ?_
  by_contra h
  apply hy
  intro i _ v
  exact Or.inl ⟨_, subset_tsupport _ (hfac y h v), rfl⟩

end GlobalTheory.AdelicCoordSupport
