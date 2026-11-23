import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_h90_preimage_trivial_at_places_over_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsConjOf σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ z ∈ U1 σ, z ∈ intU F E → ∃ x ∈ intU F E, h90 σ x = z ∧ ∀ P : HeightOneSpectrum (𝓞 E), (∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → GlobalTheory.Mem.Col2.afIso F E (z : AfE F E) P' = 1) → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1 := by
  first | exact @GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial | exact GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial | (intros; apply GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial <;> assumption)
