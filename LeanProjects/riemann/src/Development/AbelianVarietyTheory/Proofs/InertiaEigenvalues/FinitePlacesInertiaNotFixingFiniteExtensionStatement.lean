import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L], {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  first | exact @GlobalTheory.InertiaAlmostAll.finite_ramified | exact GlobalTheory.InertiaAlmostAll.finite_ramified | (intros; apply GlobalTheory.InertiaAlmostAll.finite_ramified <;> assumption)
