import Mathlib

open Matrix

namespace GlobalTheory

theorem conjTranspose_mul_mul_eq_of_form_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ z w : Fin n → E, star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w)) :
    γᴴ * J * γ = J := by
  have key : ∀ z w : Fin n → E, star z ⬝ᵥ ((γᴴ * J * γ) *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) := by
    intro z w
    rw [← h z w, star_mulVec, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  ext i j
  simpa [single_dotProduct, mulVec_single_one] using key (star (Pi.single i 1)) (Pi.single j 1)

theorem star_form_eq_of_hermitian {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (z w : Fin n → E) :
    star (star z ⬝ᵥ (J *ᵥ w)) = star w ⬝ᵥ (J *ᵥ z) := by
  rw [star_dotProduct z (J *ᵥ w), star_star, star_mulVec, ← dotProduct_mulVec, hJ]

private lemma form_sub_smul_left {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (s : E) :
    star (z - s • u) ⬝ᵥ (J *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) - star s * (star u ⬝ᵥ (J *ᵥ w)) := by
  rw [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma form_sub_smul_right {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (t : E) :
    star z ⬝ᵥ (J *ᵥ (w - t • u)) = star z ⬝ᵥ (J *ᵥ w) - t * (star z ⬝ᵥ (J *ᵥ u)) := by
  rw [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private lemma form_mulVec_eq_of_transvection {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (γ : Matrix (Fin n) (Fin n) E)
    (u : Fin n → E) (c : E)
    (hγ : ∀ v, γ *ᵥ v = v - (c * (star u ⬝ᵥ (J *ᵥ v))) • u)
    (hc : c + star c = star c * c * (star u ⬝ᵥ (J *ᵥ u))) (z w : Fin n → E) :
    star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w) := by
  have hzu := star_form_eq_of_hermitian J hJ u z
  rw [hγ z, hγ w, form_sub_smul_left, form_sub_smul_right J z u w,
    form_sub_smul_right J u u w, star_mul']
  linear_combination (c * (star u ⬝ᵥ (J *ᵥ w))) * hzu +
    (-(star (star u ⬝ᵥ (J *ᵥ z))) * (star u ⬝ᵥ (J *ᵥ w))) * hc

theorem exists_quasiReflection_mulVec_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (x y : Fin n → E)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (h0 : star (x - y) ⬝ᵥ (J *ᵥ x) ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  have hγ : ∀ v, (1 - (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ • vecMulVec (x - y) (star (x - y) ᵥ* J)) *ᵥ v
      = v - ((star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ v))) • (x - y) := by
    intro v
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
    congr 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  have hsa : star (star (x - y) ⬝ᵥ (J *ᵥ x)) = star x ⬝ᵥ (J *ᵥ (x - y)) :=
    star_form_eq_of_hermitian J hJ (x - y) x
  have hsum : star (x - y) ⬝ᵥ (J *ᵥ x) + star (star (x - y) ⬝ᵥ (J *ᵥ x))
      = star (x - y) ⬝ᵥ (J *ᵥ (x - y)) := by
    rw [hsa]
    simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
    linear_combination hxy
  have hs0 : star (star (x - y) ⬝ᵥ (J *ᵥ x)) ≠ 0 := (star_ne_zero).mpr h0
  have hc : (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ + star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
      = star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
        * (star (x - y) ⬝ᵥ (J *ᵥ (x - y))) := by
    rw [star_inv₀, ← hsum]
    field_simp
    ring
  refine ⟨_, conjTranspose_mul_mul_eq_of_form_eq J _
    (form_mulVec_eq_of_transvection J hJ _ (x - y) _ hγ hc), ?_⟩
  rw [hγ, inv_mul_cancel₀ h0, one_smul, sub_sub_cancel]

theorem exists_unitary_mulVec_eq_of_form_eq :
    ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E,
      star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 →
      ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  intro E _ _ _ n J hJ _ x y hxy hx
  by_cases h0 : star (x - y) ⬝ᵥ (J *ᵥ x) = 0
  · have hneg : star (-y) ⬝ᵥ (J *ᵥ (-y)) = star y ⬝ᵥ (J *ᵥ y) := by
      rw [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have hyx : star y ⬝ᵥ (J *ᵥ x) = star x ⬝ᵥ (J *ᵥ x) := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at h0
      exact h0.symm
    have h1 : star (x - -y) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
      rw [sub_neg_eq_add, star_add, add_dotProduct, hyx, ← two_mul]
      exact mul_ne_zero two_ne_zero hx
    obtain ⟨γ, hγ, hγx⟩ := exists_quasiReflection_mulVec_eq J hJ x (-y) (hxy.trans hneg.symm) h1
    refine ⟨-γ, ?_, ?_⟩
    · rw [conjTranspose_neg, neg_mul, mul_neg, neg_mul, neg_neg, hγ]
    · rw [neg_mulVec, hγx, neg_neg]
  · exact exists_quasiReflection_mulVec_eq J hJ x y hxy h0

end GlobalTheory
