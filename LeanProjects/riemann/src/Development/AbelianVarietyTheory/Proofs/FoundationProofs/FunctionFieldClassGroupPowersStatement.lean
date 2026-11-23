import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowers
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_class_group_powers : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  first | exact @GlobalTheory.exists_class_group_mk0_eq_mul_pow | exact GlobalTheory.exists_class_group_mk0_eq_mul_pow | (intros; apply GlobalTheory.exists_class_group_mk0_eq_mul_pow <;> assumption)
