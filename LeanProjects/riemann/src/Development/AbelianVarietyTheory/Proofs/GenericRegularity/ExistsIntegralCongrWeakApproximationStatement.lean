import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximation
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_congr_weak_approximation : ∀ (Ω : Type) [Field Ω] (ι : Type) [Finite ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))), (∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) → ∀ (i₀ : ι) (a : Ω), v i₀ a ≤ 1 → ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  first | exact @GlobalTheory.WeakApprox.exists_integral_congr | exact GlobalTheory.WeakApprox.exists_integral_congr | (intros; apply GlobalTheory.WeakApprox.exists_integral_congr <;> assumption)
