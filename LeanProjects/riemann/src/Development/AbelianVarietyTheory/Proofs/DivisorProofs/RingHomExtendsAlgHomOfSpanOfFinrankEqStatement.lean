import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEq
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B), Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O → ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  first | exact @GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | exact GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | (intros; apply GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq <;> assumption)
