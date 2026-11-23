import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n),
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsTotallyComplex E') (_ : Algebra E E')
      (_ : Algebra E' Ω) (_ : IsScalarTower E E' Ω) (_ : IsAlgClosure E' Ω) (w' : HeightOneSpectrum (𝓞 E'))
      (_ : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal ∧ ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 ∧
      normV w' = g ^ n ∧ (∃ ζ : E', IsPrimitiveRoot ζ (g ^ n - 1)) ∧
      ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
  first | exact @GlobalTheory.UnrCycExt.exists_unramified_ext | exact GlobalTheory.UnrCycExt.exists_unramified_ext | (intros; apply GlobalTheory.UnrCycExt.exists_unramified_ext <;> assumption)
