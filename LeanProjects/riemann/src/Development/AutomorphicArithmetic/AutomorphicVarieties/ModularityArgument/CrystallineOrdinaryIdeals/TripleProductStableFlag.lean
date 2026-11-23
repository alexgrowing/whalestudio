import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tripleProduct_stable_flag : ∀ {H C : Type} [Group H] [CommRing C] (I : Subgroup H) [I.Normal] (ρ : H →* GL (Fin 3) C) (ψ : Fin 3 → H →* Cˣ) (s₀ : H), s₀ ∈ I → (∀ a b, a ≠ b → IsUnit ((ψ a s₀ : C) - ψ b s₀)) → (ρ s₀ : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal (fun a => (ψ a s₀ : C)) → (∀ s : Fin 3 → H, (∀ a, s a ∈ I) → ((ρ (s 0) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ (ψ 0 (s 0) : C)) * ((ρ (s 1) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ (ψ 1 (s 1) : C)) * ((ρ (s 2) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ (ψ 2 (s 2) : C)) = 0) → (∀ g i j, j < i → (ρ g : Matrix (Fin 3) (Fin 3) C) i j = 0) ∧ ∀ s ∈ I, ∀ i, (ρ s : Matrix (Fin 3) (Fin 3) C) i i = ψ i s := by
  intro H C _ _ I _ ρ ψ s₀ hs₀ hu hD htrip
  have hdiag : ∀ c : C, (ρ s₀ : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      Matrix.diagonal (fun a => (ψ a s₀ : C) - c) := by
    intro c
    rw [hD, Matrix.scalar_apply, Matrix.diagonal_sub]
  have hmid : ∀ s ∈ I, ∀ i j : Fin 3, i ≠ 0 → j ≠ 2 →
      (ρ s : Matrix (Fin 3) (Fin 3) C) i j = if i = j then (ψ 1 s : C) else 0 := by
    intro s hs i j hi hj
    have h := htrip ![s₀, s, s₀] (by intro a; fin_cases a <;> simp [hs, hs₀])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h
    rw [hdiag, hdiag] at h
    have h2 := congrArg (fun M => M i j) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply] at h2
    rw [(hu j 2 hj).mul_left_eq_zero, (hu i 0 hi).mul_right_eq_zero, sub_eq_zero] at h2
    exact h2
  have hfirst : ∀ s ∈ I, (ρ s : Matrix (Fin 3) (Fin 3) C) 0 0 = ψ 0 s := by
    intro s hs
    have h := htrip ![s, s₀, s₀] (by intro a; fin_cases a <;> simp [hs, hs₀])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h
    rw [hdiag, hdiag] at h
    have h2 := congrArg (fun M => M 0 0) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply] at h2
    rw [(hu 0 2 (by decide)).mul_left_eq_zero, (hu 0 1 (by decide)).mul_left_eq_zero, sub_eq_zero] at h2
    simpa using h2
  have hlast : ∀ s ∈ I, (ρ s : Matrix (Fin 3) (Fin 3) C) 2 2 = ψ 2 s := by
    intro s hs
    have h := htrip ![s₀, s₀, s] (by intro a; fin_cases a <;> simp [hs, hs₀])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h
    rw [hdiag, hdiag, Matrix.diagonal_mul_diagonal] at h
    have h2 := congrArg (fun M => M 2 2) h
    simp only [Matrix.diagonal_mul, Matrix.zero_apply, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply] at h2
    rw [((hu 2 0 (by decide)).mul (hu 2 1 (by decide))).mul_right_eq_zero, sub_eq_zero] at h2
    simpa using h2
  refine ⟨fun g i j hji => ?_, fun s hs i => ?_⟩
  · have ht : g * s₀ * g⁻¹ ∈ I := ‹I.Normal›.conj_mem s₀ hs₀ g
    have hψ : ∀ a, (ψ a (g * s₀ * g⁻¹) : C) = ψ a s₀ := by
      intro a
      rw [map_mul, map_mul, map_inv, mul_comm (ψ a g), mul_inv_cancel_right]
    have hkey : (ρ (g * s₀ * g⁻¹) : Matrix (Fin 3) (Fin 3) C) * (ρ g : Matrix (Fin 3) (Fin 3) C) =
        (ρ g : Matrix (Fin 3) (Fin 3) C) * Matrix.diagonal (fun a => (ψ a s₀ : C)) := by
      rw [← hD, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
    have e : ∀ i j : Fin 3, ((ρ (g * s₀ * g⁻¹) : Matrix (Fin 3) (Fin 3) C) * (ρ g : Matrix (Fin 3) (Fin 3) C)) i j =
        (ρ g : Matrix (Fin 3) (Fin 3) C) i j * (ψ j s₀ : C) := by
      intro i j
      rw [hkey, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Fin.sum_univ_three] at e
    have u10 := hmid _ ht 1 0 (by decide) (by decide)
    have u20 := hmid _ ht 2 0 (by decide) (by decide)
    have u21 := hmid _ ht 2 1 (by decide) (by decide)
    have u11 := hmid _ ht 1 1 (by decide) (by decide)
    have u22 := hlast _ ht
    simp only [if_neg (by decide : (1 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 0),
      if_neg (by decide : (2 : Fin 3) ≠ 1), if_pos rfl, ite_true, hψ] at u10 u20 u21 u11 u22
    have p2 : ∀ j : Fin 3, j ≠ 2 → (ρ g : Matrix (Fin 3) (Fin 3) C) 2 j = 0 := by
      intro j hj
      have h := e 2 j
      rw [u20, u21, u22] at h
      have h' : (ρ g : Matrix (Fin 3) (Fin 3) C) 2 j * ((ψ j s₀ : C) - ψ 2 s₀) = 0 := by
        linear_combination -h
      exact ((hu j 2 hj).mul_left_eq_zero).mp h'
    have p10 : (ρ g : Matrix (Fin 3) (Fin 3) C) 1 0 = 0 := by
      have h := e 1 0
      rw [u10, u11, p2 0 (by decide)] at h
      have h' : (ρ g : Matrix (Fin 3) (Fin 3) C) 1 0 * ((ψ 0 s₀ : C) - ψ 1 s₀) = 0 := by
        linear_combination -h
      exact ((hu 0 1 (by decide)).mul_left_eq_zero).mp h'
    fin_cases i <;> fin_cases j <;>
      first
      | (exfalso; revert hji; decide)
      | exact p2 0 (by decide)
      | exact p2 1 (by decide)
      | exact p10
  · fin_cases i
    · exact hfirst s hs
    · simpa using hmid s hs 1 1 (by decide) (by decide)
    · exact hlast s hs

end GlobalTheory
