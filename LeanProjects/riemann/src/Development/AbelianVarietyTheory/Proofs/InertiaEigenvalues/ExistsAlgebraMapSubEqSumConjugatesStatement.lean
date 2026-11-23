import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraMapSubEqSumConjugates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  first | exact @GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates | exact GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates | (intros; apply GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates <;> assumption)
