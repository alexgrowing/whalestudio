import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w → IsPlaceOver A v ∧ normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧ (∀ ι ∈ Ine (F := K) A, ι.restrictScalars E ∈ Ine (F := E) A) ∧ ∀ (σ : G K Ω) (φ : G E Ω), IsFrob A (normV w) σ → IsFrob A (normV v) φ → σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.FrobRestrict.frob_restrict | exact GlobalTheory.FrobRestrict.frob_restrict | (intros; apply GlobalTheory.FrobRestrict.frob_restrict <;> assumption)
