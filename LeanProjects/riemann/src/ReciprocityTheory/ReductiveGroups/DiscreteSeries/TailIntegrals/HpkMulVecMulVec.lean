import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ProdIicCastLE

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem herm_UH' [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hg']

theorem herm_sum_l {α : Type*} (c : α → ℂ) (s : Finset α) (u : α → ι → ℂ) (w : ι → ℂ) :
    herm H (∑ j ∈ s, c j • u j) w = ∑ j ∈ s, c j * herm H (u j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]

theorem herm_sum_r {α : Type*} (c : α → ℂ) (s : Finset α) (u : ι → ℂ) (w : α → ι → ℂ) :
    herm H u (∑ j ∈ s, c j • w j) = ∑ j ∈ s, star (c j) * herm H u (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem mat_eq_of_mulVec' [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v])

end herm

section hpk
variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [Matrix.mulVec, dotProduct, hpk_out k r h]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ 2 * r + k - i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp
  · rw [if_neg h]
    simp only [Matrix.mulVec, dotProduct, hpk_mid k r h]
    rw [Finset.sum_eq_single i]
    · by_cases h2 : i.val = r + k <;> simp [h2]
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hpk_mulVec, if_pos (by dsimp only; omega)]
    congr 1
    ext
    dsimp only
    omega
  · rw [if_neg h]
    split_ifs with h2
    · rw [hpk_mulVec, if_neg h, if_pos h2, neg_neg]
    · rw [hpk_mulVec, if_neg h, if_neg h2]

theorem hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' fun v => by rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

variable {k r}

theorem uh_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hpk_sq]
  rw [Matrix.inv_eq_left_inv hl, hl]

theorem uh_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (uh_inv_mul hg))

theorem herm_inv {x : Mat k r} (hx : x ∈ GV k r) (g : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((x⁻¹ * g) *ᵥ v) w = herm (Hpk k r) (g *ᵥ v) (x *ᵥ w) := by
  rw [← herm_UH' (Hpk k r) hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, uh_mul_inv hx,
    Matrix.one_mul]

end hpk

section tri

theorem sub_mul_tri {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (A * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hemb : ∑ l : Fin m, A (Fin.castLE h i) (Fin.castLE h l) * B (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), A (Fin.castLE h i) l * B l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hjl : id (Fin.castLE h j) < id l := by
    show (Fin.castLE h j).val < l.val
    have := j.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hjl, mul_zero]

theorem sub_tri_mul {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (Bᴴ * A).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᴴ * A.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hemb : ∑ l : Fin m, star (B (Fin.castLE h l) (Fin.castLE h i)) * A (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), star (B l (Fin.castLE h i)) * A l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hil : id (Fin.castLE h i) < id l := by
    show (Fin.castLE h i).val < l.val
    have := i.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hil, star_zero, zero_mul]

theorem tri_sub {n m : ℕ} (h : m ≤ n) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (B.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id :=
  fun i j hij => hB (show (Fin.castLE h j).val < (Fin.castLE h i).val from hij)

end tri

section dl
variable {k r : ℕ}

def Pm (k r : ℕ) (g : Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => herm (Hpk k r) (g *ᵥ phiV' k r b) (phiV' k r a)

def cl (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : Fin (r + 1)) : ℝ≥0 :=
  ∏ j : Fin (l.val + 1), ‖τ (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)
    (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)‖₊

theorem dl_eq (l : Fin (r + 1)) (g : Mat k r) :
    Dl k r l g = ((Pm k r g).submatrix (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))
      (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))).det := rfl

theorem pm_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (x⁻¹ * g) = τᴴ * Pm k r (κ⁻¹ * g) := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [herm_inv hx, hY a, herm_sum_r]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [herm_inv hκ]

theorem pm_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (g * y) = Pm k r (g * κ) * τ := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply]
  have e : (g * y) *ᵥ phiV' k r b = ∑ c, τ c b • ((g * κ) *ᵥ phiV' k r c) := by
    rw [← Matrix.mulVec_mulVec, hY b, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, herm_sum_l]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dl_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (x⁻¹ * g)‖₊ = cl τ l * ‖Dl k r l (κ⁻¹ * g)‖₊ := by
  rw [dl_eq, dl_eq, pm_left hx hκ τ hY, sub_tri_mul _ _ _ hτ, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul,
    nnnorm_star, nnnorm_prod]
  rfl

theorem dl_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (g * y)‖₊ = cl τ l * ‖Dl k r l (g * κ)‖₊ := by
  rw [dl_eq, dl_eq, pm_right τ hY, sub_mul_tri _ _ _ hτ, Matrix.det_mul,
    Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul, nnnorm_prod, mul_comm]
  rfl

theorem fsE_fac (s : Fin (r + 1) → ℝ) (g1 g2 : Mat k r) (c : Fin (r + 1) → ℝ≥0)
    (h : ∀ l, ‖Dl k r l g1‖₊ = c l * ‖Dl k r l g2‖₊) :
    FsE k r s g1 = (∏ l, ((c l : ℝ≥0∞)) ^ (-s l)) * FsE k r s g2 := by
  unfold FsE
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [h l, ENNReal.coe_mul, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]

end dl

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
