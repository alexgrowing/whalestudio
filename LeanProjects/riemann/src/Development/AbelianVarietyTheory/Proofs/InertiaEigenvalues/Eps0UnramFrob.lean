import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem eps0_unram_frob : ∀ (D : D7) (i : D.ntw.Tw) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.ntw.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v → (∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1) ∧ ∀ σ : Gen.GE D.nd, IsFrob (F := D.host.E) A (normV v) σ → ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  intro D i v hv A hA
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ D.host.E D.nd.Om (D.ntw.l i) σ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
      simp
    unfold eps0
    rw [MonoidHom.comp_apply, h1, map_one]
  · have h1 := cycZ_of_isFrob (l := D.ntw.l i) hv hA hσ
    show algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)
      ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : ℤ_[D.ntw.l i]) = _
    rw [h1, map_natCast]

end GlobalTheory.TripleGal
