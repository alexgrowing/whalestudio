import Mathlib

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

open scoped BigOperators Matrix in
open Polynomial in

theorem _root_.GlobalTheory.eigenvector_mem_span_twistedTrace_image :
    ∀ (H K V : Type) [Group H] [Fintype H] [Field K] [CharZero K] [AddCommGroup V] [Module K V] (st : H → V →ₗ[K] V), (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (s : Set V), Submodule.span K s = ⊤ → ∀ x : V, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K ((fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) '' s) := by
  intro H K V _ _ _ _ _ _ st _ χ s hs x hx
  let P : V →ₗ[K] V := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h
  have hP : (fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) = ⇑P := by
    funext y
    simp [P, LinearMap.sum_apply]
  have hPx : P x = (Fintype.card H : K) • x := by
    rw [← hP]
    simp only [hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hxP : x = P ((Fintype.card H : K)⁻¹ • x) := by
    rw [map_smul, hPx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hP, Submodule.span_image, hs, hxP]
  exact Submodule.mem_map_of_mem Submodule.mem_top

end GlobalTheory
