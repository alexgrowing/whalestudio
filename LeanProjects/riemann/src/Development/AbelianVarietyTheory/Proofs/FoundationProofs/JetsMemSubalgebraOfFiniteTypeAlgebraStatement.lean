import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsMemSubalgebraOfFiniteTypeAlgebra
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jets_mem_subalgebra_of_finiteType_algebra : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  first | exact @GlobalTheory.jets_mem_subalgebra_of_finiteType | exact GlobalTheory.jets_mem_subalgebra_of_finiteType | (intros; apply GlobalTheory.jets_mem_subalgebra_of_finiteType <;> assumption)
