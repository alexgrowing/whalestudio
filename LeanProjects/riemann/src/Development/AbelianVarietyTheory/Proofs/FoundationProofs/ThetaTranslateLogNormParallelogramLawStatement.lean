import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateLogNormParallelogramLaw
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslateLogNorm_parallelogram_law : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g s = PowerSeries.C (GlobalTheory.ThetaTransl.cval g s) * w) →
    ∀ P Q : ℂ, (∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * P ∈ g.abelian₂) → GL3Theta.Tors1 p g.abelian₂ Q →
      GlobalTheory.ThetaTransl.logc g (P + Q) + GlobalTheory.ThetaTransl.logc g (P - Q) = 2 * GlobalTheory.ThetaTransl.logc g P + 2 * GlobalTheory.ThetaTransl.logc g Q := by
  first | exact @GlobalTheory.ThetaPar.par_holds | exact GlobalTheory.ThetaPar.par_holds | (intros; apply GlobalTheory.ThetaPar.par_holds <;> assumption)
