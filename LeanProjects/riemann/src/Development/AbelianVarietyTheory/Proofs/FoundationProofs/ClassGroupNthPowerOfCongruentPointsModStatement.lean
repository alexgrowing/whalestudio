import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsMod
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  first | exact @GlobalTheory.classGroup_nthPower_of_codim_one_mod | exact GlobalTheory.classGroup_nthPower_of_codim_one_mod | (intros; apply GlobalTheory.classGroup_nthPower_of_codim_one_mod <;> assumption)
