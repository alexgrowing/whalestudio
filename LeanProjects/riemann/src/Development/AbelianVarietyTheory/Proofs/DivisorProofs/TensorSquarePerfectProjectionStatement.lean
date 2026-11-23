import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorSquarePerfectProjection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_map_nilpotent_sub_and_pow_of_projection : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A : Type) [CommRing A] [Algebra k A] (π : A →ₐ[k] A), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : A ⊗[k] A, IsNilpotent (a - Algebra.TensorProduct.map π π a)) ∧ ∀ a : A ⊗[k] A, ∃ b : A ⊗[k] A, Algebra.TensorProduct.map π π a = Algebra.TensorProduct.map π π b ^ p) := by
  first | exact @GlobalTheory.tensorSquare_perfectProjection | exact GlobalTheory.tensorSquare_perfectProjection | (intros; apply GlobalTheory.tensorSquare_perfectProjection <;> assumption)
