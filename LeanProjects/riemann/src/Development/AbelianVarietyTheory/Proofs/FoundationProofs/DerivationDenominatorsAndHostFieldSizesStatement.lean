import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationDenominators_and_hostField_sizes : ∀ (D : D7), admG1 D → (∃ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl) ∧ Real.log D.host.d ≤ 2 * Real.log D.host.rdE ∧ 1 ≤ D.host.rdE ∧ 1 ≤ fF D ∧ Fintype.card D.what₂.Tau = fF D ∧ Module.finrank ℚ D.host.E = 2 * fF D := by
  first | exact @GlobalTheory.NormSum.letters_and_sizes | exact GlobalTheory.NormSum.letters_and_sizes | (intros; apply GlobalTheory.NormSum.letters_and_sizes <;> assumption)
