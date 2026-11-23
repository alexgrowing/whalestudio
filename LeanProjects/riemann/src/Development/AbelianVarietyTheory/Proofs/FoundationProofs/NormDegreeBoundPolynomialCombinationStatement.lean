import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_degree_bound_polynomial_combination : ∀ (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A), ∃ (c : ℕ) (lam : Fin n → k),
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) → (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < d) → (∑ i, (C (lam i) * X ^ d + p i) • b i) ≠ 0 ∧ (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c) := by
  first | exact @GlobalTheory.NormDegree.natDegree_norm_of_coord_degree | exact GlobalTheory.NormDegree.natDegree_norm_of_coord_degree | (intros; apply GlobalTheory.NormDegree.natDegree_norm_of_coord_degree <;> assumption)
