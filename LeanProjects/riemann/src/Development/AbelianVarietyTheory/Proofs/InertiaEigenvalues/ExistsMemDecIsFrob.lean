import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem exists_mem_Dec_isFrob : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.E)) (A : ValuationSubring D.nd.Om), IsPlaceOver (F := D.host.E) A v → ∃ σ : Gen.GE D.nd, σ ∈ Dec (F := D.host.E) A ∧ IsFrob (F := D.host.E) A (normV v) σ := by
  intro D v A hA
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
  exact ⟨σ, hσ.1, hσ⟩

end GlobalTheory.TripleGal
