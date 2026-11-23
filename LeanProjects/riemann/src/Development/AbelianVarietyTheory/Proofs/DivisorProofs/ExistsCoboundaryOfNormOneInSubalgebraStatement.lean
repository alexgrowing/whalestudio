import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfNormOneInSubalgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')), (∀ x ∈ B, x.map s ∈ B) → ∀ ε : GL (Fin n) F', (ε : Matrix (Fin n) (Fin n) F') ∈ B → nrm s ε = 1 → ∃ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ∧ ε = x⁻¹ * galAct F F' n s x := by
  first | (exact @GlobalTheory.HilbertNinety.hilbert90_matrix_subalgebra_norm_one) | (exact GlobalTheory.HilbertNinety.hilbert90_matrix_subalgebra_norm_one) | (intros; apply GlobalTheory.HilbertNinety.hilbert90_matrix_subalgebra_norm_one  <;> assumption)
