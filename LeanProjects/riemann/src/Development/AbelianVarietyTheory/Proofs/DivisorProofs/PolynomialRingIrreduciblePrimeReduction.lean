import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGramSize
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_ring_irreducible_prime_reduction : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A, IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  first | (exact @GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (exact GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (intros; apply GlobalTheory.TrBasisQuot.trBasis_mod_irreducible  <;> assumption)
