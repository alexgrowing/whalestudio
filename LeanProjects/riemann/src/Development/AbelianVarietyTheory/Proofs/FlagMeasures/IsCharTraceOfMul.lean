import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem isChar_trace_of_mul {M V : Type} [Group M] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : M → Module.End ℂ V) (hT : ∀ a b, T (a * b) = T a * T b) :
    IsChar (fun m => LinearMap.trace ℂ V (T m)) := by
  have hmem : ∀ m v, T m v ∈ LinearMap.range (T 1) := fun m v =>
    ⟨T m v, by rw [← Module.End.mul_apply, ← hT, one_mul]⟩
  let ρ : Representation ℂ M (LinearMap.range (T 1)) :=
    { toFun := fun m => (T m).restrict (fun v _ => hmem m v)
      map_one' := by
        refine LinearMap.ext ?_
        rintro ⟨_, v, rfl⟩
        refine Subtype.ext ?_
        show T 1 (T 1 v) = T 1 v
        rw [← Module.End.mul_apply, ← hT, one_mul]
      map_mul' := fun a b => by
        refine LinearMap.ext fun v => Subtype.ext ?_
        show T (a * b) v = T a (T b v)
        rw [hT]; rfl }
  refine ⟨FDRep.of ρ, fun m => ?_⟩
  exact LinearMap.trace_restrict_eq_of_forall_mem _ (T m) (hmem m) (fun v _ => hmem m v)

theorem sum_fibre_one {P M : Type} [Group P] [Fintype P] [Group M] (π : P →* M) (hπ : Function.Surjective π)
    (m : M) : (∑ x : P, if π x = m then (1 : ℂ) else 0) = (Nat.card π.ker : ℂ) := by
  obtain ⟨x₀, rfl⟩ := hπ m
  rw [← Equiv.sum_comp (Equiv.mulLeft x₀)]
  simp only [Equiv.coe_mulLeft, map_mul, mul_eq_left]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MonoidHom.mem_ker]

theorem isChar_fibre_mean : ∀ (P M : Type) [Group P] [Fintype P] [Group M] [Fintype M] (π : P →* M) (χ : P → ℂ),
    Function.Surjective π → IsChar χ →
    IsChar (fun m : M => (Nat.card π.ker : ℂ)⁻¹ * ∑ x : P, if π x = m then χ x else 0) := by
  intro P M _ _ _ _ π χ hπ ⟨V, hV⟩
  have hc : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let S : M → Module.End ℂ V := fun m => ∑ x : P, if π x = m then V.ρ x else 0
  have hS : ∀ a b, S a * S b = (Nat.card π.ker : ℂ) • S (a * b) := by
    intro a b
    rw [← sum_fibre_one π hπ a, Finset.sum_smul]
    simp only [S]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : π x = a
    · rw [if_pos hx, if_pos hx, one_smul, Finset.mul_sum,
        ← Equiv.sum_comp (Equiv.mulLeft x) (fun y => if π y = a * b then V.ρ y else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Equiv.coe_mulLeft, map_mul, hx, mul_right_inj]
      split_ifs <;> simp
    · rw [if_neg hx, if_neg hx, zero_mul, zero_smul]
  have h := isChar_trace_of_mul (fun m => (Nat.card π.ker : ℂ)⁻¹ • S m) (fun a b => by
    rw [smul_mul_smul_comm, hS, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one])
  convert h using 2 with m
  rw [map_smul, smul_eq_mul]
  congr 1
  simp only [S]
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [← hV]; rfl
  · simp

end GlobalTheory.GLm
