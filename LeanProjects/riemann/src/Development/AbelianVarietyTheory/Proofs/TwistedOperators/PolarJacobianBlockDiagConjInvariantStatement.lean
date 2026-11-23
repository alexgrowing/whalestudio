import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarJacobian_blockDiag_conj_invariant : ∀ (p q : ℕ) (k k' Y : Mat p q), k * k' = 1 → IsKC k → IsKC k' → polJ (k * Y * k') = polJ Y := by
  first | exact @GlobalTheory.PolarU.Conj.polJ_conj | exact GlobalTheory.PolarU.Conj.polJ_conj | (intros; apply GlobalTheory.PolarU.Conj.polJ_conj <;> assumption)
