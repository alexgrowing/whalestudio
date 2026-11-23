import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSubfieldValuationClosure
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfield_valuation_closure' : ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U), ∃ S' : Subfield U, ∀ u, u ∈ S' ↔ ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  first | exact @GlobalTheory.exists_subfield_valuation_closure | exact GlobalTheory.exists_subfield_valuation_closure | (intros; apply GlobalTheory.exists_subfield_valuation_closure <;> assumption)
