import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem lu_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem lu_up {R : Type} [CommRing R] (U k T : Matrix (Fin 3) (Fin 3) R) (e : U * k = k * T)
    (hU : ∀ a b, wt a b < 0 → U a b = 0) (hT : ∀ a b, wt a b < 0 → T a b = 0)
    (hu : ∀ a b, a ≠ b → IsUnit (U a a - T b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have t10 := hT 1 0 (by decide)
  have t20 := hT 2 0 (by decide)
  have t21 := hT 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, t10, t20, t21] at e10 e20 e21
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e10; linear_combination e10)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem lu_J {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_upper :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (r : D →* GG 3 R) (x : D),
      Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Upper η r → ∀ g a b, wt a b < 0 → (r g).mat a b = 0 := by
  intro O R D _ _ _ _ _ _ η Ψ r x hr hx hΨ hU g
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hU g hg
  have hX : ∀ x a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro x a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ * x⁻¹ * g := ⟨_, rfl⟩
  have hηy : η y = 1 := by simp [hy, hx]
  have hΨy : Ψ y = (Ψ x)⁻¹ := by simp [hy]
  have rx : (r x).right = 1 := (hr.mult x).trans hx
  have ry : (r y).right = 1 := (hr.mult y).trans hηy
  have rg : (r g).right = -1 := (hr.mult g).trans hg
  have e0 : r x * r g = r g * (r y)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hy]; congr 1; group
  have e1 : (r x).left * (r g).left = (r g).left * theta ((r y).left⁻¹) := by
    have := congrArg SemidirectProduct.left e0
    simpa [rx, ry, rg] using this
  have e2 : (r x).mat * (r g).mat = (r g).mat * (Jmat R 3 * (r y).matᵀ * Jmat R 3) := by
    have := congrArg Units.val e1
    rwa [Units.val_mul, Units.val_mul, theta_val, inv_inv] at this
  refine lu_up _ _ _ e2 (hU x hx) (fun a b hab => ?_) (fun a b hab => ?_)
  · rw [lu_J]
    refine hU y hηy _ _ ?_
    have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    rwa [this]
  · have w : wt1 b.rev = -wt1 b := by fin_cases b <;> rfl
    rw [lu_J, ← residue_ne_zero_iff_isUnit, map_sub, hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit, hΨy, w, _root_.inv_zpow', neg_neg]
    exact (lu_unit (Ψ x) hΨ a b hab).map _
