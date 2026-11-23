import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcTame

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.LlcTame

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
private theorem eq_one_of_isSemisimple_of_charpoly_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hs : f.IsSemisimple)
    (hc : f.charpoly = (X - 1) ^ Module.finrank ℂ V) : f = 1 := by
  have hn : IsNilpotent (f - 1) := by
    refine ⟨Module.finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa using this
  have hs' : (f - 1).IsSemisimple :=
    hs.sub_of_commute (Commute.one_right f) Module.End.isSemisimple_id
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hs')

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
theorem _root_.GlobalTheory.LlcTame.isTameWD_iff_charPol : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (y : _root_.GlobalTheory.WeilDeligne.WD h), _root_.GlobalTheory.LocLanglands.IsTameWD y ↔
    ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) →
      y.charPol σ = (X - 1) ^ y.lpDim := by
  intro E Ω _ _ _ _ _ A w h y
  unfold _root_.GlobalTheory.LocLanglands.IsTameWD
  constructor
  · rintro ⟨n, a, rfl, ha⟩ σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    refine (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).trans ?_
    rw [hd, ha σ hσ, LinearMap.charpoly_one]
  · intro H
    obtain ⟨n, a, rfl⟩ := y.exists_rep
    refine ⟨n, a, rfl, fun σ hσ => ?_⟩
    have hc := H σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    rw [hd] at hc
    have hc' := (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).symm.trans hc
    exact eq_one_of_isSemisimple_of_charpoly_eq _ (a.semisimple σ) hc'
