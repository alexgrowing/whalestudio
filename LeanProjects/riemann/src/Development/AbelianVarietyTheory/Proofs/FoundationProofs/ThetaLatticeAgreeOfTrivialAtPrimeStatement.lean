import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeAgreeOfTrivialAtPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  first | exact @GlobalTheory.NormSum.La_agree_of_trivAt | exact GlobalTheory.NormSum.La_agree_of_trivAt | (intros; apply GlobalTheory.NormSum.La_agree_of_trivAt <;> assumption)
