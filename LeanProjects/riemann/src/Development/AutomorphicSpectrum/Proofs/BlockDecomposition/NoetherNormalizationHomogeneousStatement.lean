import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneous
import Mathlib
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_homogeneous : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)), I ≠ ⊤ → (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∃ (e m : ℕ) (y : Fin m → MvPolynomial (Fin (N + 1)) K), 0 < e ∧ (∀ i, (y i).IsHomogeneous e) ∧ AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧ Module.Finite (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
  first | exact @GlobalTheory.CompanionTheory.ConeNoether.main | exact GlobalTheory.CompanionTheory.ConeNoether.main | (intros; apply GlobalTheory.CompanionTheory.ConeNoether.main <;> assumption)
