import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeSelfDual
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_selfDual : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), SelfDual (gamA ψ) (latA D cc N N') := by
  first | exact @GlobalTheory.FinWeil.LatSelfDual.latA_selfDual | exact GlobalTheory.FinWeil.LatSelfDual.latA_selfDual | (intros; apply GlobalTheory.FinWeil.LatSelfDual.latA_selfDual <;> assumption)
