import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPullback_firstGroup_rationalPoint_eq_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  first | exact @GlobalTheory.RatRow.pull_eq_smul_iop | exact GlobalTheory.RatRow.pull_eq_smul_iop | (intros; apply GlobalTheory.RatRow.pull_eq_smul_iop <;> assumption)
