import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_integralPoints_membership : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  first | exact @GlobalTheory.NormSum.mem_ratG_intG | exact GlobalTheory.NormSum.mem_ratG_intG | (intros; apply GlobalTheory.NormSum.mem_ratG_intG <;> assumption)
