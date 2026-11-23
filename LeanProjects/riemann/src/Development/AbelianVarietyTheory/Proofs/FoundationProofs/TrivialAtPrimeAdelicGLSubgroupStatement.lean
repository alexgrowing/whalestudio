import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialAtPrime_adelicGL_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧ (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧ ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  first | exact @GlobalTheory.TrivSubgroup.trivAt_subgroup | exact GlobalTheory.TrivSubgroup.trivAt_subgroup | (intros; apply GlobalTheory.TrivSubgroup.trivAt_subgroup <;> assumption)
