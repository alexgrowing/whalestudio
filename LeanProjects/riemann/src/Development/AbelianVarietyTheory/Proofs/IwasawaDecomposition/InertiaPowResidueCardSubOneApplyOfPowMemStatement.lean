import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  first | exact @GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | exact GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | (intros; apply GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem <;> assumption)
