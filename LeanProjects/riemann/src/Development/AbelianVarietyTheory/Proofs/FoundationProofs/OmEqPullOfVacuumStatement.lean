import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), (∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) → ∀ (W : WeilO D cc δ N N' e0) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → (W.Om γA γA' e0 = fun z => a * pull D (tor0 D cc δ) γ γ' e0 z) → ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om γA γA' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z := by
  first | exact @GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum | exact GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum | (intros; apply GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum <;> assumption)
