import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharTraceMulIdempotent
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumConjIdempotentEqCardSmul

open GlobalTheory.BI

namespace GlobalTheory.BI

theorem character_eq_ind_of_imprimitive :
    ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  intro L _ _ G _ _ V _ _ _ ρ T e hirr he0 hee hT hoff
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun t => LinearMap.trace L V (ρ t * e), ?_, ?_⟩
  · exact isChar_trace_mul_idempotent L T V (ρ.comp T.subtype) e hee (fun t => hT t t.2)
  · intro g
    have hsum := GlobalTheory.sum_conj_idempotent_eq_card_smul L G V ρ T e hirr he0 hee hT hoff
    have hcard : (Nat.card T : L) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := T)).ne'
    have hkey : ∀ h : G, LinearMap.trace L V (ρ h * e)
        = ext0 T (fun t : T => LinearMap.trace L V (ρ t * e)) h := by
      intro h
      unfold ext0
      split_ifs with hh
      · rfl
      · have h2 : ρ h * e = ρ h * e * e := by rw [mul_assoc, hee]
        rw [h2, LinearMap.trace_mul_comm, ← mul_assoc, hoff h hh, map_zero]
    have hterm : ∀ x : G, LinearMap.trace L V (ρ g * (ρ x * e * ρ x⁻¹))
        = LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      intro x
      rw [show ρ g * (ρ x * e * ρ x⁻¹) = (ρ g * ρ x * e) * ρ x⁻¹ by simp only [mul_assoc],
        LinearMap.trace_mul_comm]
      simp only [map_mul, mul_assoc]
    have htr : (Nat.card T : L) * LinearMap.trace L V (ρ g)
        = ∑ x : G, LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      have h3 : (Nat.card T : L) * LinearMap.trace L V (ρ g)
          = LinearMap.trace L V (ρ g * ∑ x : G, ρ x * e * ρ x⁻¹) := by
        rw [hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
      rw [h3, Finset.mul_sum, map_sum]
      exact Finset.sum_congr rfl (fun x _ => hterm x)
    rw [Representation.character, ind, finsum_eq_sum_of_fintype]
    simp only [← hkey]
    rw [← htr, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end GlobalTheory.BI
