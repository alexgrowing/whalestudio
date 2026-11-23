import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (k : GL (Fin N) (AE D)) L₁ → Moves D (k' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ x' ∈ La D (tor0 D cc δ) L₂ L₂', W.Om h h' (Wd D (tor0 D cc δ) x F) = Wd D (tor0 D cc δ) x' (W.Om h h' F) := by
  first | exact @GlobalTheory.WeilEquiv.om_wd_moved | exact GlobalTheory.WeilEquiv.om_wd_moved | (intros; apply GlobalTheory.WeilEquiv.om_wd_moved <;> assumption)
