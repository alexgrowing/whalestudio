import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDivisibleChainPrimaryTorsionGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisible_chain_primary_torsion_group : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X], (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} → (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  first | exact @GlobalTheory.Ord2.DivChain.exists_divisible_chain | exact GlobalTheory.Ord2.DivChain.exists_divisible_chain | (intros; apply GlobalTheory.Ord2.DivChain.exists_divisible_chain <;> assumption)
