import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_lift_of_residual_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A → (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) → ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  first | exact @GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | exact GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | (intros; apply GlobalTheory.InertiaLift.exists_mem_Ine_eq_on <;> assumption)
