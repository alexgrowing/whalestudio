import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HermitianProjections

section proj

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def prj (H : Matrix n n ℂ) (V : Matrix n ι ℂ) : Matrix ι n ℂ := (Vᴴ * H * V)⁻¹ * Vᴴ * H

def rhoOf (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + V * (Φ - 1) * prj H V

lemma prj_mul (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    prj H V * V = 1 := by
  have h := Matrix.nonsing_inv_mul _ hΓ
  have e : prj H V * V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H * V) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, h]

lemma K_eq (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    Vᴴ * H = (Vᴴ * H * V) * prj H V := by
  have h := Matrix.mul_nonsing_inv _ hΓ
  have e : (Vᴴ * H * V) * prj H V = ((Vᴴ * H * V) * (Vᴴ * H * V)⁻¹) * (Vᴴ * H) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, h, Matrix.one_mul]

lemma prj_perp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (x : n → ℂ) (hx : (Vᴴ * H) *ᵥ x = 0) :
    prj H V *ᵥ x = 0 := by
  have e : prj H V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

lemma decomp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (x : n → ℂ) :
    (Vᴴ * H) *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = 0 := by
  have hK := K_eq H V hΓ
  have e : (Vᴴ * H) *ᵥ (V *ᵥ (prj H V *ᵥ x)) = ((Vᴴ * H * V) * prj H V) *ᵥ x := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [Matrix.mulVec_sub, e, ← hK, sub_self]

lemma rhoOf_mul (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    rhoOf H V Φ * V = V * Φ := by
  simp only [rhoOf]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (V * (Φ - 1)), prj_mul H V hΓ, Matrix.mul_one,
    Matrix.mul_sub, Matrix.mul_one]
  abel

lemma rhoOf_perp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (x : n → ℂ)
    (hx : (Vᴴ * H) *ᵥ x = 0) : rhoOf H V Φ *ᵥ x = x := by
  simp only [rhoOf]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, prj_perp H V x hx, Matrix.mulVec_zero,
    add_zero]

lemma eq_rhoOf (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det)
    (g : Matrix n n ℂ) (hg : g * V = V * Φ) (hgU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → g *ᵥ x = x) :
    g = rhoOf H V Φ := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  simp only [Matrix.toLin'_apply]
  have hd := decomp H V hΓ x
  have h1 : g *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x) := hgU _ hd
  have h2 : rhoOf H V Φ *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x) :=
    rhoOf_perp H V Φ _ hd
  have h3 : ∀ w : ι → ℂ, g *ᵥ (V *ᵥ w) = rhoOf H V Φ *ᵥ (V *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg, rhoOf_mul H V Φ hΓ]
  have hx : x = (x - V *ᵥ (prj H V *ᵥ x)) + V *ᵥ (prj H V *ᵥ x) := (sub_add_cancel x _).symm
  rw [hx, Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, h3]

lemma rhoOf_sub_one_pow (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ)
    (hΓ : IsUnit (Vᴴ * H * V).det) (m : ℕ) :
    (rhoOf H V Φ - 1) ^ (m + 1) = V * (Φ - 1) ^ (m + 1) * prj H V := by
  have hW : rhoOf H V Φ - 1 = V * (Φ - 1) * prj H V := by
    simp only [rhoOf, add_sub_cancel_left]
  have hP := prj_mul H V hΓ
  induction m with
  | zero => rw [zero_add, pow_one, pow_one, hW]
  | succ k ih =>
    rw [pow_succ (rhoOf H V Φ - 1) (k + 1), ih, hW]
    calc V * (Φ - 1) ^ (k + 1) * prj H V * (V * (Φ - 1) * prj H V)
        = V * (Φ - 1) ^ (k + 1) * (prj H V * V) * (Φ - 1) * prj H V := by
          simp only [Matrix.mul_assoc]
      _ = V * (Φ - 1) ^ (k + 1 + 1) * prj H V := by
          rw [hP, Matrix.mul_one, pow_succ (Φ - 1) (k + 1), Matrix.mul_assoc V ((Φ - 1) ^ (k + 1)) (Φ - 1)]

end proj

lemma strict_pow_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    ∀ p : ℕ, ∀ i j : Fin m, j.val < i.val + p → (M ^ p) i j = 0 := by
  intro p
  induction p with
  | zero =>
    intro i j hij
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun h => by subst h; omega)
  | succ p ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < i.val + p
    · rw [ih i k hk, zero_mul]
    · rw [hM k j (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]

lemma strict_pow_eq_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    M ^ m = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact strict_pow_apply M hM m i j (by have := j.isLt; omega)

lemma pow_eq_zero_of_le {R : Type*} [MonoidWithZero R] {x : R} {p q : ℕ} (h : x ^ p = 0)
    (hpq : p ≤ q) : x ^ q = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [pow_add, h, zero_mul]

section herm

variable {n : Type*} [Fintype n]

lemma herm_add_left (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

lemma herm_add_right (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_smul_left (H : Matrix n n ℂ) (c : ℂ) (a w : n → ℂ) : herm H (c • a) w = c * herm H a w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_smul_right (H : Matrix n n ℂ) (c : ℂ) (v a : n → ℂ) : herm H v (c • a) = conj c * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  rfl

lemma herm_sub_left (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a - b) w = herm H a w - herm H b w := by
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub]

lemma herm_sub_right (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a - b) = herm H v a - herm H v b := by
  simp only [herm, star_sub, sub_dotProduct]

lemma herm_zero_left (H : Matrix n n ℂ) (w : n → ℂ) : herm H 0 w = 0 := by
  simp only [herm, Matrix.mulVec_zero, dotProduct_zero]

lemma herm_zero_right (H : Matrix n n ℂ) (v : n → ℂ) : herm H v 0 = 0 := by
  simp only [herm, star_zero, zero_dotProduct]

lemma herm_mulVec {m ι κ : Type*} [Fintype m] [Fintype ι] [Fintype κ] (H : Matrix m m ℂ)
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    herm H (A *ᵥ a) (B *ᵥ b) = star b ⬝ᵥ ((Bᴴ * H * A) *ᵥ a) := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end herm

section uni

variable {n : Type*} [Fintype n] [DecidableEq n]

end uni

section sig

lemma star_mul_real (a : ℝ) (x : ℂ) : (star x * ((a : ℂ) * x)).re = a * Complex.normSq x := by
  simp [Complex.mul_re, Complex.normSq_apply]
  try ring

lemma sig_split {p q : ℕ} (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (ψ₁ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ)) (h₁ : ∀ c, ψ₁ c = 0 → (star c ⬝ᵥ (G *ᵥ c)).re ≤ 0)
    (ψ₂ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin q → ℂ)) (h₂ : ∀ c, ψ₂ c = 0 → 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUnit Q.det ∧ Qᴴ * G * Q = fromBlocks 1 0 0 (-1) := by
  classical
  set U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ↑hG.eigenvectorUnitary with hUd
  set lam := hG.eigenvalues with hlam
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
  have hspec : G = U * diagonal (RCLike.ofReal ∘ lam) * star U := by
    have := hG.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hD : Uᴴ * G * U = diagonal (fun i => (lam i : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rfl
  have hform : ∀ c, star (U *ᵥ c) ⬝ᵥ (G *ᵥ (U *ᵥ c)) = ∑ i, star (c i) * ((lam i : ℂ) * c i) := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have hlam0 : ∀ i, lam i ≠ 0 := by
    have h1 : Uᴴ.det * U.det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hUU, Matrix.det_one]
    have hdD : (diagonal (fun i => (lam i : ℂ))).det ≠ 0 := by
      rw [← hD, Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, h1, mul_one]
      exact hdet
    rw [Matrix.det_diagonal] at hdD
    intro i
    have := (Finset.prod_ne_zero_iff.mp hdD) i (Finset.mem_univ i)
    exact_mod_cast this

  have hext : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (d : Fin p ⊕ Fin q → ℂ),
      (∀ i, d i = if h : P i then c ⟨i, h⟩ else 0) →
      ∑ i, star (d i) * ((lam i : ℂ) * d i) = ∑ j : {i // P i}, star (c j) * ((lam j.1 : ℂ) * c j) := by
    intro P _ c d hd
    rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => star (d i) * ((lam i : ℂ) * d i))]
    have h0 : ∑ i : {x // ¬ P x}, star (d i.1) * ((lam i.1 : ℂ) * d i.1) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [hd, dif_neg i.2]; simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd, dif_pos i.2]
  have hEv : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (i : Fin p ⊕ Fin q),
      ((Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // P i}) => if i = j.1 then (1 : ℂ) else 0) *ᵥ c) i =
        if h : P i then c ⟨i, h⟩ else 0 := by
    intro P _ c i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i, h⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; exact hb (Subtype.ext e.symm)
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; exact h (e ▸ b.2)
  have hcardP : Fintype.card {i // 0 < lam i} ≤ p := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // 0 < lam i} → ℂ) →ₗ[ℂ] (Fin p → ℂ) := ψ₁ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₁ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₁ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hpos : 0 < ∑ j : {i // 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // 0 < lam i} => lam j.1 * Complex.normSq (c j))
        (fun j _ => mul_nonneg j.2.le (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
    linarith
  have hcardN : Fintype.card {i // ¬ 0 < lam i} ≤ q := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // ¬ 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // ¬ 0 < lam i} → ℂ) →ₗ[ℂ] (Fin q → ℂ) := ψ₂ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₂ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₂ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hneg : ∀ j : {i // ¬ 0 < lam i}, lam j.1 < 0 := fun j => lt_of_le_of_ne (not_lt.mp j.2) (hlam0 j.1)
    have hpos : 0 < ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // ¬ 0 < lam i} => (-lam j.1) * Complex.normSq (c j))
        (fun j _ => mul_nonneg (neg_nonneg.mpr (hneg j).le) (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos (neg_pos.mpr (hneg j)) (Complex.normSq_pos.mpr hj)
    have e : ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) =
        -∑ j : {i // ¬ 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      rw [← Finset.sum_neg_distrib]; simp only [neg_mul]
    linarith
  have hsum : Fintype.card {i // 0 < lam i} + Fintype.card {i // ¬ 0 < lam i} = p + q := by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => 0 < lam i), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have hp : Fintype.card {i // 0 < lam i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < lam i} = q := by omega
  set e₁ := Fintype.equivFinOfCardEq hp
  set e₂ := Fintype.equivFinOfCardEq hq
  set e : Fin p ⊕ Fin q ≃ Fin p ⊕ Fin q := (Equiv.sumCongr e₁.symm e₂.symm).trans (Equiv.sumCompl fun i => 0 < lam i)
  have he1 : ∀ j, 0 < lam (e (Sum.inl j)) := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (e₁.symm j).2
  have he2 : ∀ j, lam (e (Sum.inr j)) < 0 := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact lt_of_le_of_ne (not_lt.mp (e₂.symm j).2) (hlam0 _)
  set s : Fin p ⊕ Fin q → ℂ := fun i => (((Real.sqrt |lam i|)⁻¹ : ℝ) : ℂ)
  set A := U * diagonal s
  have hA : Aᴴ * G * A = diagonal (fun i => ((lam i / |lam i| : ℝ) : ℂ)) := by
    have : Aᴴ * G * A = (diagonal s)ᴴ * (Uᴴ * G * U) * diagonal s := by
      simp only [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hab : 0 < |lam i| := abs_pos.mpr (hlam0 i)
    have hsq : Real.sqrt |lam i| * Real.sqrt |lam i| = |lam i| := Real.mul_self_sqrt hab.le
    have hsne : Real.sqrt |lam i| ≠ 0 := (Real.sqrt_pos.mpr hab).ne'
    simp only [s, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    rw [Real.sq_sqrt hab.le]
    ring
  have hQ : (A.submatrix id e)ᴴ * G * A.submatrix id e = fromBlocks 1 0 0 (-1) := by
    have : (A.submatrix id e)ᴴ * G * A.submatrix id e = (Aᴴ * G * A).submatrix e e := by
      ext a b; rfl
    rw [this, hA, Matrix.submatrix_diagonal_equiv]
    have h1 : ∀ j, ((lam (e (Sum.inl j)) / |lam (e (Sum.inl j))| : ℝ) : ℂ) = 1 := by
      intro j; rw [abs_of_pos (he1 j), div_self (he1 j).ne']; simp
    have h2 : ∀ j, ((lam (e (Sum.inr j)) / |lam (e (Sum.inr j))| : ℝ) : ℂ) = -1 := by
      intro j; rw [abs_of_neg (he2 j), div_neg, div_self (he2 j).ne]; simp
    have hfe : (fun i => ((lam i / |lam i| : ℝ) : ℂ)) ∘ e = Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)) := by
      funext x
      cases x with
      | inl j => exact h1 j
      | inr j => exact h2 j
    rw [hfe, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one]
    congr 1
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨A.submatrix id e, ?_, hQ⟩
  have hdB : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
      Fintype.card_fin]
    exact pow_ne_zero _ (by norm_num)
  rw [← hQ, Matrix.det_mul, Matrix.det_mul] at hdB
  exact isUnit_iff_ne_zero.mpr (fun h => hdB (by rw [h, mul_zero]))

end sig

end Formalism.FourierDecayAlt.P.HermitianProjections
