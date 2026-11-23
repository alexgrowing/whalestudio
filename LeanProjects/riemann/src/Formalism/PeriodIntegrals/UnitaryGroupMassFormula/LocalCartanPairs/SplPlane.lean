import Mathlib

noncomputable section

open Matrix

namespace PI.LocCartanPair

variable {R : Type} [CommRing R] [StarRing R]

theorem splPlane_entry {ι m n : Type} [Fintype ι] (A : Matrix ι ι R) (M : Matrix ι m R)
    (N : Matrix ι n R) (r : m) (s : n) :
    (Mᴴ * A * N) r s = star (fun i => M i r) ⬝ᵥ (A *ᵥ fun i => N i s) := by
  rw [Matrix.mul_assoc]; rfl

theorem splPlane_herm {ι : Type} [Fintype ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (a b : ι → R) :
    star (star a ⬝ᵥ (A *ᵥ b)) = star b ⬝ᵥ (A *ᵥ a) := by
  rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec, hA]

theorem splPlane_unitEntry [IsLocalRing R] {ι : Type} [Fintype ι] (w z : ι → R)
    (h : w ⬝ᵥ z = 1) : ∃ i, IsUnit (z i) := by
  by_contra hn
  push Not at hn
  have hm : w ⬝ᵥ z ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hn i))
  rw [h] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm isUnit_one

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def splBasis (E : Fin 2 ⊕ κ ≃ ι) (x y : ι → R) : Matrix ι (Fin 2 ⊕ κ) R :=
  fun i c => Sum.elim (fun a => ![x, y] a i) (fun j => (1 : Matrix ι ι R) i (E (.inr j))) c

def splCorr (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (x y : ι → R) : Matrix (Fin 2) κ R :=
  fun a j => ![-(star y ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j)))),
    -(star x ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j))))] a

theorem splPlane_core (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (hA : Aᴴ = A) (x y : ι → R)
    (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1)
    (hdet : IsUnit (x (E (.inl 0)) * y (E (.inl 1)) - y (E (.inl 0)) * x (E (.inl 1)))) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  set u₀ := splBasis E x y with hu₀def
  set B := splCorr E A x y with hBdef
  set T : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks 1 B 0 1 with hTdef
  set T' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks 1 (-B) 0 1 with hT'def
  have hTT' : T * T' = 1 := by simp [hTdef, hT'def, fromBlocks_multiply, fromBlocks_one]
  have hT'T : T' * T = 1 := by simp [hTdef, hT'def, fromBlocks_multiply, fromBlocks_one]
  set S : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := u₀.submatrix E id with hSdef
  have hS : S = fromBlocks S.toBlocks₁₁ 0 S.toBlocks₂₁ 1 := by
    conv_lhs => rw [← fromBlocks_toBlocks S]
    congr 1
    · ext a j; simp [hSdef, hu₀def, splBasis, toBlocks₁₂, one_apply]
    · ext k j; simp [hSdef, hu₀def, splBasis, toBlocks₂₂, one_apply]
  have hSdet : IsUnit S.det := by
    rw [hS, det_fromBlocks_zero₁₂, det_one, mul_one, det_fin_two]
    simpa [hSdef, hu₀def, splBasis, toBlocks₁₁] using hdet
  set v₀ : Matrix (Fin 2 ⊕ κ) ι R := S⁻¹.submatrix id E.symm with hv₀def
  have hu₀S : u₀ = S.submatrix E.symm id := by ext i c; simp [hSdef]
  have huv₀ : u₀ * v₀ = 1 := by
    rw [hu₀S, hv₀def, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      mul_nonsing_inv _ hSdet, submatrix_one_equiv]
  have hvu₀ : v₀ * u₀ = 1 := by
    rw [hu₀S, hv₀def, submatrix_mul_equiv, nonsing_inv_mul _ hSdet, submatrix_id_id]
  set u := u₀ * T with hudef
  set v := T' * v₀ with hvdef
  have huv : u * v = 1 := by
    rw [hudef, hvdef, Matrix.mul_assoc, ← Matrix.mul_assoc T, hTT', Matrix.one_mul, huv₀]
  have hvu : v * u = 1 := by
    rw [hudef, hvdef, Matrix.mul_assoc, ← Matrix.mul_assoc v₀, hvu₀, Matrix.one_mul, hT'T]
  have hc0 : (fun i => u i (.inl 0)) = x := by
    funext i; simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  have hc1 : (fun i => u i (.inl 1)) = y := by
    funext i; simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  have hcj : ∀ j, (fun i => u i (.inr j)) = (fun i => (1 : Matrix ι ι R) i (E (.inr j)))
      + B 0 j • x + B 1 j • y := by
    intro j; funext i
    simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, one_apply]
    ring
  set G := uᴴ * A * u with hGdef
  have hG : ∀ r s, G r s = star (fun i => u i r) ⬝ᵥ (A *ᵥ fun i => u i s) :=
    fun r s => splPlane_entry A u u r s
  have h12 : G.toBlocks₁₂ = 0 := by
    ext a j
    simp only [toBlocks₁₂, of_apply, hG, hcj, Matrix.zero_apply]
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, hc0, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hxx, hxy, hBdef, splCorr]
      simp
    · simp only [Fin.mk_one, Fin.isValue, hc1, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hyx, hyy, hBdef, splCorr]
      simp
  have h21 : G.toBlocks₂₁ = 0 := by
    ext j a
    have := congrFun (congrFun h12 a) j
    simp only [toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply] at this ⊢
    rw [hG, ← splPlane_herm A hA, ← hG, this, star_zero]
  have h11 : G.toBlocks₁₁ = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [toBlocks₁₁, hG, hc0, hc1, hxx, hyy, hxy, hyx]
  have hGe : G = fromBlocks !![0, 1; 1, 0] 0 0 G.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [h11, h12, h21]
  refine ⟨u, v, G.toBlocks₂₂, huv, hvu, fun i => congrFun hc0 i, fun i => congrFun hc1 i,
    hGe, ?_, ?_⟩
  · ext i j
    simp only [conjTranspose_apply, toBlocks₂₂, of_apply]
    rw [hG, hG, splPlane_herm A hA]
  · intro hAdet
    set U : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := u.submatrix E id with hUdef
    have hUv : U * v.submatrix id E = 1 := by
      rw [hUdef, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, huv,
        submatrix_one_equiv]
    have hU : IsUnit U.det := isUnit_det_of_right_inverse hUv
    have hGU : G = Uᴴ * A.submatrix E E * U := by
      rw [hUdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
        submatrix_id_id]
    have hGdet : IsUnit G.det := by
      rw [hGU, det_mul, det_mul, det_conjTranspose, det_submatrix_equiv_self]
      exact (hU.star.mul hAdet).mul hU
    rw [hGe, det_fromBlocks_zero₁₂] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet

section Local

variable {R : Type} [CommRing R] [StarRing R]

theorem splPlane_pair [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hA : Aᴴ = A) (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ i₀ j₀, i₀ ≠ j₀ ∧ IsUnit (x i₀ * y j₀ - y i₀ * x j₀) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  rw [dotProduct_mulVec] at hyx
  obtain ⟨i₀, hi₀⟩ := splPlane_unitEntry _ _ hyx
  obtain ⟨xi, hxi⟩ := hi₀.exists_right_inv
  set y' := y - (y i₀ * xi) • x with hy'
  have hy'i : y' i₀ = 0 := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(y i₀)) * hxi
  have hxy' : (star x ᵥ* A) ⬝ᵥ y' = 1 := by
    rw [← dotProduct_mulVec, hy', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxx,
      hxy, smul_eq_mul, mul_zero, sub_zero]
  obtain ⟨j₀, hj₀⟩ := splPlane_unitEntry _ _ hxy'
  have hne : i₀ ≠ j₀ := by
    rintro rfl; rw [hy'i] at hj₀; exact not_isUnit_zero hj₀
  refine ⟨i₀, j₀, hne, ?_⟩
  have e : x i₀ * y j₀ - y i₀ * x j₀ = x i₀ * y' j₀ := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y i₀ * x j₀) * hxi
  rw [e]; exact hi₀.mul hj₀

def splEquiv {ι : Type} [DecidableEq ι] (i₀ j₀ : ι) (hne : i₀ ≠ j₀) :
    Fin 2 ⊕ {j // j ≠ i₀ ∧ j ≠ j₀} ≃ ι where
  toFun := Sum.elim ![i₀, j₀] Subtype.val
  invFun j := if h0 : j = i₀ then .inl 0 else if h1 : j = j₀ then .inl 1 else .inr ⟨j, h0, h1⟩
  left_inv := by
    rintro (a | ⟨j, h0, h1⟩)
    · fin_cases a
      · simp
      · simp [hne.symm]
    · simp [h0, h1]
  right_inv := by
    intro j
    by_cases h0 : j = i₀
    · subst h0; simp
    · by_cases h1 : j = j₀
      · subst h1; simp [h0]
      · simp [h0, h1]

theorem splPlane [IsLocalRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hc : Fintype.card κ + 2 = Fintype.card ι) (A : Matrix ι ι R) (hA : Aᴴ = A)
    (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  obtain ⟨i₀, j₀, hne, hu⟩ := splPlane_pair A hA x y hxx hxy
  have hc₀ : Fintype.card {j // j ≠ i₀ ∧ j ≠ j₀} = Fintype.card κ := by
    have := Fintype.card_congr (splEquiv i₀ j₀ hne)
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  let E : Fin 2 ⊕ κ ≃ ι :=
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivOfCardEq hc₀).symm).trans (splEquiv i₀ j₀ hne)
  have h0 : E (.inl 0) = i₀ := by simp [E, splEquiv]
  have h1 : E (.inl 1) = j₀ := by simp [E, splEquiv]
  exact splPlane_core E A hA x y hxx hyy hxy (by rw [h0, h1]; exact hu)

end Local

end PI.LocCartanPair
