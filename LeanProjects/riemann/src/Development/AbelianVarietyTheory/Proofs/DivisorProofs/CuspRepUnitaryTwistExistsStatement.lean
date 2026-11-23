import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepUnitaryTwistExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_unitary_twist_exists : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CG E a), 1 ≤ a →
    ∃ ν : Formalism.L2.Host.HChar E, (∀ w, ν.UnrAt w) ∧ (π.twist ν).IsUnitary := by
  first | exact @GlobalTheory.CuspRep.exists_unramified_twist_isUnitary | exact GlobalTheory.CuspRep.exists_unramified_twist_isUnitary | (intros; apply GlobalTheory.CuspRep.exists_unramified_twist_isUnitary <;> assumption)
