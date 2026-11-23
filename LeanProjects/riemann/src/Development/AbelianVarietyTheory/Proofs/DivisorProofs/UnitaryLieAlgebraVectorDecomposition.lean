import Mathlib
open scoped Matrix ComplexOrder

namespace GlobalTheory.LieIwasawa

variable {n : ℕ}

theorem star_sd (a b : Fin n → ℂ) : star (star a ⬝ᵥ b) = star b ⬝ᵥ a := by
  simp [dotProduct, mul_comm]

theorem star_dot_mulVec (D : Matrix (Fin n) (Fin n) ℂ) (hD : Dᴴ = D) (a b : Fin n → ℂ) :
    star a ⬝ᵥ D *ᵥ b = star (D *ᵥ a) ⬝ᵥ b := by
  rw [Matrix.star_mulVec, hD, Matrix.dotProduct_mulVec]

theorem orth (D : Matrix (Fin n) (Fin n) ℂ) (hD : Dᴴ = D) (a b : Fin n → ℂ)
    (ha : D *ᵥ a = a) (hb : D *ᵥ b = -b) : star a ⬝ᵥ b = 0 ∧ star b ⬝ᵥ a = 0 := by
  have h1 := star_dot_mulVec D hD a b
  have h2 := star_dot_mulVec D hD b a
  rw [ha, hb] at h1 h2
  simp only [dotProduct_neg, star_neg, neg_dotProduct] at h1 h2
  constructor
  · linear_combination (-1/2 : ℂ) * h1
  · linear_combination (1/2 : ℂ) * h2

theorem exists_skew (D : Matrix (Fin n) (Fin n) ℂ) (hD : Dᴴ = D) (s : ℂ) (hs : star s = s)
    (u x : Fin n → ℂ) (hu : D *ᵥ u = s • u) (hx : D *ᵥ x = s • x) (hr : star x ⬝ᵥ x ≠ 0)
    (him : star x ⬝ᵥ u + star u ⬝ᵥ x = 0) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ = -Z ∧ D * Z = Z * D ∧ Z *ᵥ x = u ∧
      ∀ y, star x ⬝ᵥ y = 0 → star u ⬝ᵥ y = 0 → Z *ᵥ y = 0 := by
  set r := star x ⬝ᵥ x with hrdef
  set q := star u ⬝ᵥ x with hq
  have hrs : star r = r := by
    rw [hrdef, star_sd]
  have hqs : star q = -q := by
    have : star q = star x ⬝ᵥ u := by rw [hq, star_sd]
    rw [this]; linear_combination him
  have hu' : star u ᵥ* D = s • star u := by
    have := congrArg star hu
    rw [Matrix.star_mulVec, hD, star_smul, hs] at this
    exact this
  have hx' : star x ᵥ* D = s • star x := by
    have := congrArg star hx
    rw [Matrix.star_mulVec, hD, star_smul, hs] at this
    exact this
  have hmv : ∀ a b y : Fin n → ℂ, Matrix.vecMulVec a b *ᵥ y = (b ⬝ᵥ y) • a := by
    intro a b y
    ext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨r⁻¹ • (Matrix.vecMulVec u (star x) - Matrix.vecMulVec x (star u)) +
    (q / r ^ 2) • Matrix.vecMulVec x (star x), ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_vecMulVec, star_star, star_inv₀, star_div₀, star_pow, hrs, hqs]
    module
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hu, hx, hu', hx',
      Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
  · simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, hmv, ← hrdef, ← hq]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · intro y h1 h2
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, hmv, h1, h2]

theorem decomp_of_involution (D : Matrix (Fin n) (Fin n) ℂ) (hD : Dᴴ = D) (hDD : D * D = 1)
    (x : Fin n → ℂ) (hx : star x ⬝ᵥ D *ᵥ x = 0) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : Xᴴ * D + D * X = 0) :
    ∃ (Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), Zᴴ = -Z ∧ Zᴴ * D + D * Z = 0 ∧
      (X - Z) *ᵥ x = c • x := by
  have split : ∀ y : Fin n → ℂ, ∃ a b : Fin n → ℂ, D *ᵥ a = a ∧ D *ᵥ b = -b ∧ y = a + b := by
    intro y
    refine ⟨(1/2 : ℂ) • (y + D *ᵥ y), (1/2 : ℂ) • (y - D *ᵥ y), ?_, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec,
        add_comm]
    · rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec]
      module
    · module
  by_cases h0 : x = 0
  · exact ⟨0, 0, by simp, by simp, by simp [h0]⟩
  obtain ⟨p, m, hp, hm, hxs⟩ := split x
  obtain ⟨a, b, ha, hb, hv⟩ := split (X *ᵥ x)
  have hDx : D *ᵥ x = p - m := by rw [hxs, Matrix.mulVec_add, hp, hm, sub_eq_add_neg]
  have hDv : D *ᵥ (X *ᵥ x) = a - b := by rw [hv, Matrix.mulVec_add, ha, hb, sub_eq_add_neg]
  obtain ⟨pm, mp⟩ := orth D hD p m hp hm
  obtain ⟨pb, bp⟩ := orth D hD p b hp hb
  obtain ⟨am, ma⟩ := orth D hD a m ha hm
  have hrho : star p ⬝ᵥ p = star m ⬝ᵥ m := by
    rw [hDx, hxs] at hx
    simp only [star_add, add_dotProduct, dotProduct_sub, pm, mp] at hx
    linear_combination hx
  have hp0 : star p ⬝ᵥ p ≠ 0 := by
    intro h
    have h' := h
    rw [hrho] at h'
    rw [dotProduct_star_self_eq_zero] at h h'
    exact h0 (by rw [hxs, h, h', add_zero])
  have hm0 : star m ⬝ᵥ m ≠ 0 := hrho ▸ hp0
  have hkey : star a ⬝ᵥ p + star p ⬝ᵥ a = star b ⬝ᵥ m + star m ⬝ᵥ b := by
    have h1 : star x ⬝ᵥ (Xᴴ * D + D * X) *ᵥ x = 0 := by simp [hX]
    rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star x) Xᴴ, ← Matrix.star_mulVec, hDx, hDv, hv] at h1
    nth_rewrite 1 [hxs] at h1
    simp only [star_add, add_dotProduct, dotProduct_sub, pb, bp, am, ma] at h1
    linear_combination h1
  set r := star p ⬝ᵥ p with hr
  set l : ℂ := (star a ⬝ᵥ p + star p ⬝ᵥ a) / (2 * r) with hl
  have hrs : star r = r := by
    rw [hr, star_sd]
  have hls : star l = l := by
    have e1 : star (star a ⬝ᵥ p) = star p ⬝ᵥ a := by rw [star_sd]
    have e2 : star (star p ⬝ᵥ a) = star a ⬝ᵥ p := by rw [star_sd]
    rw [hl, star_div₀, star_add, e1, e2, star_mul', hrs, add_comm]
    simp
  have hl2 : l * (2 * r) = star a ⬝ᵥ p + star p ⬝ᵥ a := by
    rw [hl]; field_simp
  obtain ⟨Z₁, s1, c1, e1, k1⟩ := exists_skew D hD 1 (by simp) (a - l • p) p
    (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, hp, one_smul]) (by rw [hp, one_smul]) hp0
    (by
      simp only [star_sub, star_smul, hls, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, ← hr]
      linear_combination -hl2)
  obtain ⟨Z₂, s2, c2, e2, k2⟩ := exists_skew D hD (-1) (by simp) (b - l • m) m
    (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hb, hm]; module) (by rw [hm]; module) hm0
    (by
      simp only [star_sub, star_smul, hls, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, ← hrho]
      linear_combination -hl2 - hkey)
  have z1 : Z₁ *ᵥ m = 0 := k1 m pm (by
    simp only [star_sub, star_smul, sub_dotProduct, smul_dotProduct, am, pm]; simp)
  have z2 : Z₂ *ᵥ p = 0 := k2 p mp (by
    simp only [star_sub, star_smul, sub_dotProduct, smul_dotProduct, bp, mp]; simp)
  have hs : (Z₁ + Z₂)ᴴ = -(Z₁ + Z₂) := by rw [Matrix.conjTranspose_add, s1, s2, neg_add]
  refine ⟨Z₁ + Z₂, l, hs, ?_, ?_⟩
  · rw [hs, Matrix.mul_add, c1, c2, Matrix.neg_mul, Matrix.add_mul, neg_add_cancel]
  · rw [Matrix.sub_mulVec, hv, hxs, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
      e1, e2, z1, z2]
    module

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Matrix (Fin n) (Fin n) ℂ),
    D = Matrix.diagonal (fun i => if ε i then 1 else -1) →
    ∀ x : Fin n → ℂ, star x ⬝ᵥ D *ᵥ x = 0 → ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * D + D * X = 0 →
      ∃ (Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), Zᴴ = -Z ∧ Zᴴ * D + D * Z = 0 ∧
        (X - Z) *ᵥ x = c • x := by
  intro n ε D hD x hx X hX
  refine decomp_of_involution D ?_ ?_ x hx X hX
  · rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : ε i <;> simp [h]
  · rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : ε i <;> simp [h]

end GlobalTheory.LieIwasawa
