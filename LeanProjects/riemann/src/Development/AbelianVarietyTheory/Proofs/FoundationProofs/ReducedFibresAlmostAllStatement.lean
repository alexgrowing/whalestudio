import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedFibresAlmostAll
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_sub_C_not_mem_sq_maximal : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2 := by
  first | exact @GlobalTheory.reduced_fibres_almost_all | exact GlobalTheory.reduced_fibres_almost_all | (intros; apply GlobalTheory.reduced_fibres_almost_all <;> assumption)
