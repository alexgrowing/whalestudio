import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MatExtBvec

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section herm
variable {n : ℕ}

theorem dot_bvec (i : Fin n) (x : Fin n → ℂ) : star (bvec i) ⬝ᵥ x = x i := by
  unfold dotProduct
  rw [Finset.sum_eq_single i]
  · simp [bvec]
  · intro b _ hb; simp [bvec, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bvec_self (i : Fin n) : bvec i i = 1 := by simp [bvec]

theorem bvec_ne (i j : Fin n) (h : i.val ≠ j.val) : bvec i j = 0 := by
  unfold bvec; rw [Pi.single_apply, if_neg (fun e => h (congrArg Fin.val e).symm)]

theorem herm_bb (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : herm H (bvec i) (bvec j) = H j i := by
  unfold herm; rw [dot_bvec, mv_bvec]

theorem herm_add_l (H : Matrix (Fin n) (Fin n) ℂ) (v v' w : Fin n → ℂ) :
    herm H (v + v') w = herm H v w + herm H v' w := by
  unfold herm; rw [mulVec_add, dotProduct_add]

theorem herm_smul_l (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) : herm H (c • v) w = c * herm H v w := by
  unfold herm; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (v w w' : Fin n → ℂ) :
    herm H v (w + w') = herm H v w + herm H v w' := by
  unfold herm; rw [star_add, add_dotProduct]

theorem herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = star c * herm H v w := by
  unfold herm; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_sum_l (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by
  unfold herm; rw [Matrix.mulVec_sum, dotProduct_sum]

theorem herm_zero_l (H : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) : herm H 0 w = 0 := by
  unfold herm; rw [mulVec_zero, dotProduct_zero]

theorem herm_mul (H g : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem herm_UH (H g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  rw [herm_mul, show gᴴ * H * g = H from hg]

end herm

theorem herm_hpk_r (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v (Hpk k r *ᵥ w) = star w ⬝ᵥ v := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, hpk_conjT, mulVec_mulVec, hpk_mul, one_mulVec]

theorem sq2_mul_sq2_eq_half : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  try push_cast
  rw [← mul_inv, h2]; norm_num

theorem star_inv_sqrt_two : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  try push_cast
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]

section phi
variable (k n : ℕ)

theorem hpk_ww (j j' : Fin (k + 1)) :
    Hpk k n (wI k n j) (wI k n j') = if j = j' then (if j.val = k then -1 else 1) else 0 := by
  rw [hpk_apply]
  have hj := j.2
  have e1 : (wI k n j).val = n + j.val := rfl
  have e2 : (wI k n j').val = n + j'.val := rfl
  have hs : sg k n (n + j.val) = n + j.val := by unfold sg; rw [if_neg (by omega)]
  rw [e1, e2, hs]
  by_cases h : j = j'
  · subst h; rw [if_pos rfl, if_pos rfl]
    by_cases h' : j.val = k
    · rw [if_pos (by omega : n + j.val = n + k), if_pos h']
    · rw [if_neg (by omega : ¬ n + j.val = n + k), if_neg h']
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by omega)))]

theorem phi_iso (hk : 1 ≤ k) (a b : Fin (n + 1)) : herm (Hpk k n) (phiV k n a) (phiV k n b) = 0 := by
  unfold phiV
  split_ifs with ha hb hb
  · rw [herm_bb, hpk_apply]; simp only [esI, Fin.val_mk]; unfold sg; split_ifs <;> first | omega | rfl
  · unfold epsV
    rw [herm_smul_r, herm_add_r, herm_bb, herm_bb, hpk_apply, hpk_apply]
    simp only [esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]; unfold sg; split_ifs <;> first | omega | simp
  · unfold epsV
    rw [herm_smul_l, herm_add_l, herm_bb, herm_bb, hpk_apply, hpk_apply]
    simp only [esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]; unfold sg; split_ifs <;> first | omega | simp
  · unfold epsV
    have h0l : (0 : Fin (k + 1)) ≠ Fin.last k := fun h => by have := congrArg Fin.val h; simp at this; omega
    rw [herm_smul_l, herm_smul_r, herm_add_l, herm_add_r, herm_add_r, herm_bb, herm_bb, herm_bb, herm_bb]
    have hk0 : (0 : ℕ) ≠ k := by omega
    simp [hpk_ww, h0l, h0l.symm, hk0]

theorem eps_dot (hk : 1 ≤ k) : star (epsV k n) ⬝ᵥ epsV k n = 1 := by
  unfold epsV
  have hne : (wI k n 0).val ≠ (wI k n (Fin.last k)).val := by simp only [wI, Fin.val_zero, Fin.val_last]; omega
  rw [star_smul, star_inv_sqrt_two, smul_dotProduct, dotProduct_smul, star_add, add_dotProduct, dot_bvec, dot_bvec]
  simp only [Pi.add_apply, bvec_self, bvec_ne _ _ hne, bvec_ne _ _ (Ne.symm hne), smul_eq_mul]
  linear_combination 2 * sq2_mul_sq2_eq_half

theorem phi_dot (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    star (phiV k n b) ⬝ᵥ phiV k n a = if a = b then 1 else 0 := by
  have hv : a = b ↔ a.val = b.val := Fin.ext_iff
  unfold phiV
  split_ifs with ha hb hab hb hab hb hab hb hab
  · subst hab; rw [dot_bvec, bvec_self]
  · rw [dot_bvec, bvec_ne]; simp only [esI, Fin.val_mk]; omega
  · omega
  · unfold epsV
    rw [dot_bvec, Pi.smul_apply, Pi.add_apply, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · omega
  · unfold epsV
    rw [star_smul, smul_dotProduct, star_add, add_dotProduct, dot_bvec, dot_bvec, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · exact eps_dot k n hk
  · omega

theorem phi_pair (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    herm (Hpk k n) (phiV k n a) (phiV' k n b) = if a = b then 1 else 0 := by
  unfold phiV'; rw [herm_hpk_r, phi_dot k n hk]

theorem mphi_li (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    LinearIndependent ℂ (fun a => m *ᵥ phiV k n a) := by
  rw [Fintype.linearIndependent_iff]; intro g hg b
  have h : herm (Hpk k n) (∑ a, g a • (m *ᵥ phiV k n a)) (m *ᵥ phiV' k n b) =
      herm (Hpk k n) 0 (m *ᵥ phiV' k n b) := by rw [hg]
  rw [herm_zero_l, herm_sum_l] at h
  simp only [herm_smul_l, herm_UH _ _ hm, phi_pair k n hk, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

theorem iw_apply (hIW : IW) (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    ∃ κ : Mat k n, κ ∈ GV k n ∧ κᴴ * κ = 1 ∧ ∃ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, m *ᵥ phiV k n a = ∑ b, τ b a • (κ *ᵥ phiV k n b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k n l (fun a => m *ᵥ phiV k n a) := by
  obtain ⟨κ0, hκ0, τ, hτ, hrep, hprod⟩ := hIW k n (fun a => m *ᵥ phiV k n a) hk (mphi_li k n hk m hm)
    (fun a b => by
      show herm (Hpk k n) (m *ᵥ phiV k n a) (m *ᵥ phiV k n b) = 0
      rw [herm_UH _ _ hm, phi_iso k n hk])
  have hG : κ0ᴴ * Hpk k n * κ0 = Hpk k n := hκ0.1
  have hU : κ0ᴴ * κ0 = 1 := hκ0.2
  refine ⟨κ0 * Hpk k n, ?_, ?_, τ, hτ, fun a => ?_, hprod⟩
  · show (κ0 * Hpk k n)ᴴ * Hpk k n * (κ0 * Hpk k n) = Hpk k n
    rw [conjTranspose_mul, hpk_conjT]
    calc Hpk k n * κ0ᴴ * Hpk k n * (κ0 * Hpk k n) = Hpk k n * (κ0ᴴ * Hpk k n * κ0) * Hpk k n := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k n := by rw [hG, hpk_mul, Matrix.one_mul]
  · rw [conjTranspose_mul, hpk_conjT]
    calc Hpk k n * κ0ᴴ * (κ0 * Hpk k n) = Hpk k n * (κ0ᴴ * κ0) * Hpk k n := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hpk_mul]
  · rw [show m *ᵥ phiV k n a = ∑ b, τ b a • (κ0 *ᵥ phiV' k n b) from hrep a]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold phiV'; rw [Matrix.mulVec_mulVec]

end phi

section gram

theorem sum_castLE {M : Type} [AddCommMonoid M] {n l : ℕ} (h : l + 1 ≤ n) (f : Fin n → M)
    (hf : ∀ b : Fin n, l < b.val → f b = 0) : ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE h)))]
  · rw [Finset.sum_image (fun a _ b _ e => Fin.castLE_injective h e)]
  · intro b _ hb; apply hf; by_contra hc; push Not at hc
    exact hb (Finset.mem_image.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩)

theorem prod_Iic {M : Type} [CommMonoid M] {n : ℕ} (l : Fin (n + 1)) (f : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Iic l, f j = ∏ j : Fin (l.val + 1), f (Fin.castLE (by omega) j) := by
  apply Finset.prod_nbij' (fun a => (⟨min a.val l.val, by omega⟩ : Fin (l.val + 1))) (Fin.castLE (by omega))
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_Iic, Fin.le_def]; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; ext; simp; omega
  · intro a _; ext; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; congr 1; ext; simp; omega

theorem gram_mat' {N L : ℕ} (X : Fin L → Fin N → ℂ) (Xm : Matrix (Fin N) (Fin L) ℂ) (hX : ∀ p a, Xm p a = X a p) :
    (Matrix.of fun a b => star (X a) ⬝ᵥ X b) = Xmᴴ * Xm := by
  ext a b; simp [Matrix.mul_apply, dotProduct, conjTranspose_apply, hX]

theorem det_gram_tri {N L : ℕ} (Z : Fin L → Fin N → ℂ) (T : Matrix (Fin L) (Fin L) ℂ) (hT : T.BlockTriangular id) :
    (Matrix.of fun a b => star (∑ j, T j a • Z j) ⬝ᵥ ∑ j, T j b • Z j).det =
      (star (∏ j, T j j) * ∏ j, T j j) * (Matrix.of fun a b => star (Z a) ⬝ᵥ Z b).det := by
  rw [gram_mat' (fun a => ∑ j, T j a • Z j) ((Matrix.of fun p a => Z a p) * T) (fun p a => by
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _),
    gram_mat' Z (Matrix.of fun p a => Z a p) (fun p a => rfl), conjTranspose_mul]
  rw [show Tᴴ * (Matrix.of fun p a => Z a p)ᴴ * ((Matrix.of fun p a => Z a p) * T) =
      Tᴴ * ((Matrix.of fun p a => Z a p)ᴴ * (Matrix.of fun p a => Z a p)) * T by simp only [Matrix.mul_assoc]]
  rw [det_mul, det_mul, det_conjTranspose, det_of_upperTriangular hT]; ring

theorem ga_tri (k r : ℕ) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (l : Fin (r + 1)) :
    Ga k r l (fun a => ∑ b, τ b a • Z b) = (∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2) * Ga k r l Z := by
  have h : l.val + 1 ≤ r + 1 := by omega
  have hs : ∀ a : Fin (l.val + 1), (∑ b, τ b (Fin.castLE h a) • Z b) =
      ∑ j : Fin (l.val + 1), τ (Fin.castLE h j) (Fin.castLE h a) • Z (Fin.castLE h j) := by
    intro a; apply sum_castLE h; intro b hb
    rw [hτ (show id (Fin.castLE h a) < id b by simp only [id, Fin.lt_def, Fin.val_castLE]; omega), zero_smul]
  have hT : (τ.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro i j hij; simp only [submatrix_apply]; apply hτ
    simp only [id, Fin.lt_def, Fin.val_castLE] at hij ⊢; exact hij
  unfold Ga
  simp only [hs]
  have key := det_gram_tri (fun j => Z (Fin.castLE h j)) (τ.submatrix (Fin.castLE h) (Fin.castLE h)) hT
  simp only [submatrix_apply] at key
  rw [key, prod_Iic l, show star (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) * ∏ j, τ (Fin.castLE h j) (Fin.castLE h j) =
      ((Complex.normSq (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) : ℝ) : ℂ) from (Complex.normSq_eq_conj_mul_self).symm,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, norm_prod, ← Finset.prod_pow]

theorem ga_unit (k r : ℕ) (U : Mat k r) (hU : Uᴴ * U = 1) (l : Fin (r + 1)) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => U *ᵥ Z a) = Ga k r l Z := by
  unfold Ga; simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]

end gram

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
