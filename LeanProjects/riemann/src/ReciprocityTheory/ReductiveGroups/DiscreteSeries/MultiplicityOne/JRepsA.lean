import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem sg_val_in {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) : sg k r i = i := by
  simp [sg, h]

theorem sg_val_out {i : Fin (2 * r + k + 1)} (h : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) :
    (sg k r i).val = 2 * r + k - i.val := by
  simp [sg, h]

theorem sg_sg (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k
  · rw [sg_val_in h, sg_val_in h]
  · have h1 := sg_val_out h
    have h2 : ¬ (r ≤ (sg k r i).val ∧ (sg k r i).val ≤ r + k) := by
      have := i.isLt; omega
    apply Fin.ext; rw [sg_val_out h2, h1]; have := i.isLt; omega

theorem eq_sg_iff {i j : Fin (2 * r + k + 1)} : i = sg k r j ↔ j = sg k r i := by
  constructor
  · rintro rfl; rw [sg_sg]
  · rintro rfl; rw [sg_sg]

def mono {n : ℕ} (s : Fin n → Fin n) (a : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun l j => if l = s j then a j else 0

theorem mul_mono {n : ℕ} (s : Fin n → Fin n) (a : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M * mono s a) i j = M i (s j) * a j := by
  rw [mul_apply]
  simp only [mono, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem conjT_mono_mul {n : ℕ} (s : Fin n → Fin n) (a : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((mono s a)ᴴ * M) i j = star (a i) * M (s i) j := by
  rw [mul_apply]
  simp only [mono, of_apply, conjTranspose_apply, apply_ite, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def bt (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if hj : j.val < r then c ⟨j.val, hj⟩
  else if hj2 : j.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - j.val, by have := j.isLt; omega⟩))⁻¹

theorem bigCell_one_mono (c : Fin r → ℂ) :
    bigCell k r c 1 = mono (sg k r) (bt k r c) := by
  funext i j
  unfold bigCell bt mono; rw [of_apply]
  by_cases hj : j.val < r
  · have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
    simp only [dif_pos hj]
    congr 1
    apply propext; constructor
    · rintro rfl; apply Fin.ext; rw [hs]; simp [esI]
    · rintro rfl; apply Fin.ext; rw [hs]; simp [esI]
  · simp only [dif_neg hj]
    by_cases hj2 : j.val ≤ r + k
    · have hs := sg_val_in (k := k) (r := r) (i := j) ⟨by omega, hj2⟩
      simp only [dif_pos hj2, hs]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, one_apply]
        congr 1
        apply propext; constructor
        · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
        · rintro rfl; rfl
      · rw [dif_neg hi, if_neg]
        rintro rfl; exact hi ⟨by omega, hj2⟩
    · have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
      simp only [dif_neg hj2]
      congr 1
      apply propext; constructor
      · intro h; apply Fin.ext; rw [hs]; omega
      · rintro rfl; rw [hs]

def et (k r : ℕ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ j.val ∧ j.val ≤ r + k then (if j.val = r + k then -1 else 1) else 1

theorem Hpk_mono : Hpk k r = mono (sg k r) (et k r) := by
  funext i j
  unfold Hpk et mono; rw [of_apply]; beta_reduce
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hs := sg_val_in (k := k) (r := r) (i := j) hj
    rw [hs, if_pos hj]
    by_cases hij : i = j
    · subst hij
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hj.1, hj.2, rfl⟩, if_pos rfl]
    · rw [if_neg (by intro h; apply hij; apply Fin.ext; omega), if_neg (by intro h; apply hij; apply Fin.ext; omega),
        if_neg (by intro h; exact hij h.2.2), if_neg hij]
  · have hs := sg_val_out (k := k) (r := r) (i := j) hj
    rw [if_neg hj]
    by_cases hij : i = sg k r j
    · have hv : i.val = 2 * r + k - j.val := by rw [hij, hs]
      rw [if_pos hij]
      by_cases hir : i.val < r
      · rw [if_pos ⟨hir, by have := j.isLt; omega⟩]
      · rw [if_neg (by omega), if_pos ⟨by omega, by have := j.isLt; omega⟩]
    · have hv : i.val ≠ 2 * r + k - j.val := by intro h; apply hij; apply Fin.ext; rw [hs, h]
      rw [if_neg hij, if_neg (by omega), if_neg (by omega), if_neg (by intro h; apply hj; omega)]

theorem bt_sg_lt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : j.val < r) :
    bt k r c (sg k r j) = (star (c ⟨j.val, hj⟩))⁻¹ := by
  have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
  unfold bt
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 3; apply Fin.ext; simp only [hs]; have := j.isLt; omega

theorem bt_sg_gt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : r + k < j.val) :
    bt k r c (sg k r j) = c ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ := by
  have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
  unfold bt
  rw [dif_pos (by omega)]
  congr 1; apply Fin.ext; simp only [hs]

theorem bt_gt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : r + k < j.val) :
    bt k r c j = (star (c ⟨2 * r + k - j.val, by have := j.isLt; omega⟩))⁻¹ := by
  unfold bt; rw [dif_neg (by omega), dif_neg (by omega)]

theorem bt_lt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : j.val < r) :
    bt k r c j = c ⟨j.val, hj⟩ := by
  unfold bt; rw [dif_pos hj]

theorem bt_in (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    bt k r c j = 1 := by
  unfold bt; rw [dif_neg (by omega), dif_pos hj.2]

theorem et_out {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) : et k r j = 1 := by
  unfold et; rw [if_neg hj]

theorem sg_out {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) :
    ¬ (r ≤ (sg k r j).val ∧ (sg k r j).val ≤ r + k) := by
  rw [sg_val_out hj]; have := j.isLt; omega

theorem bigCell_one_unitary (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    (bigCell k r c 1)ᴴ * Hpk k r * bigCell k r c 1 = Hpk k r := by
  rw [bigCell_one_mono]
  ext i j
  rw [mul_mono, conjT_mono_mul, Hpk_mono]
  simp only [mono, of_apply]
  by_cases hij : i = sg k r j
  · subst hij
    rw [sg_sg, if_pos rfl, if_pos rfl]
    by_cases hj : j.val < r
    · rw [bt_sg_lt c hj, bt_lt c hj, et_out (sg_out (by omega)), et_out (by omega)]
      rw [star_inv₀, star_star, mul_one]; exact inv_mul_cancel₀ (hc _)
    · by_cases hj2 : j.val ≤ r + k
      · rw [sg_val_in ⟨by omega, hj2⟩, bt_in c ⟨by omega, hj2⟩]; simp
      · rw [bt_sg_gt c (by omega), bt_gt c (by omega), et_out (sg_out (by omega)), et_out (by omega), mul_one]
        exact mul_inv_cancel₀ (by rw [Ne, star_eq_zero]; exact hc _)
  · rw [if_neg hij, if_neg, mul_zero, zero_mul]
    intro h; apply hij; simpa only [sg_sg] using congrArg (sg k r) h

theorem bigCell_star_mul (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    bigCell k r (star c) 1 * bigCell k r c 1 = 1 := by
  rw [bigCell_one_mono, bigCell_one_mono]
  ext i j
  rw [mul_mono]
  simp only [mono, of_apply, sg_sg, one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
    by_cases hj : i.val < r
    · rw [bt_sg_lt _ hj, bt_lt c hj]; simp only [Pi.star_apply, star_star]; exact inv_mul_cancel₀ (hc _)
    · by_cases hj2 : i.val ≤ r + k
      · rw [sg_val_in ⟨by omega, hj2⟩, bt_in _ ⟨by omega, hj2⟩, bt_in _ ⟨by omega, hj2⟩, mul_one]
      · rw [bt_sg_gt _ (by omega), bt_gt c (by omega)]; simp only [Pi.star_apply]
        exact mul_inv_cancel₀ (by rw [Ne, star_eq_zero]; exact hc _)
  · rw [if_neg hij, if_neg hij, zero_mul]

theorem bigCell_map_conj (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).map (starRingEnd ℂ) = bigCell k r (star c) (μ.map (starRingEnd ℂ)) := by
  ext i j
  simp only [map_apply, bigCell, Pi.star_apply]
  split_ifs <;> simp

def wbE (k r : ℕ) (v : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then v ⟨i.val - r, by omega⟩ else 0

theorem wI_val' (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

theorem wI_in (j : Fin (k + 1)) : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
  rw [wI_val']; have := j.isLt; omega

theorem wI_sub (j : Fin (k + 1)) : (⟨(wI k r j).val - r, by rw [wI_val']; omega⟩ : Fin (k + 1)) = j := by
  apply Fin.ext; simp [wI_val']

theorem wbE_wI (v : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : wbE k r v (wI k r j) = v j := by
  unfold wbE; rw [dif_pos (wI_in j)]; congr 1; exact wI_sub j

theorem sum_wb {f : Fin (2 * r + k + 1) → ℂ} (hf : ∀ i : Fin (2 * r + k + 1), ¬ (r ≤ i.val ∧ i.val ≤ r + k) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  have hinj : Function.Injective (wI k r) := by
    intro a b h; apply Fin.ext; have := congrArg Fin.val h; rw [wI_val', wI_val'] at this; omega
  rw [show (∑ j : Fin (k + 1), f (wI k r j)) = ∑ i ∈ Finset.univ.map ⟨wI k r, hinj⟩, f i from (Finset.sum_map Finset.univ ⟨wI k r, hinj⟩ f).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  intro h
  apply hi
  refine Finset.mem_map.2 ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext; simp only [Function.Embedding.coeFn_mk, wI_val']; omega

theorem embWb_in (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : r ≤ i.val ∧ i.val ≤ r + k) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    embWb k r X i j = X ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ := by
  unfold embWb; rw [dif_pos ⟨hi, hj⟩]

theorem embWb_out_left (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) : embWb k r X i j = if i = j then 1 else 0 := by
  unfold embWb; rw [dif_neg (fun h => hi h.1)]
  by_cases h : i = j
  · rw [if_pos ⟨h, hi⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

theorem embWb_out_right (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) : embWb k r X i j = if i = j then 1 else 0 := by
  unfold embWb; rw [dif_neg (fun h => hj h.2)]
  by_cases h : i = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

theorem embWb_mulVec (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (k + 1) → ℂ) :
    embWb k r X *ᵥ wbE k r v = wbE k r (X *ᵥ v) := by
  funext i
  simp only [mulVec, dotProduct]
  rw [sum_wb (f := fun l => embWb k r X i l * wbE k r v l) (by intro l hl; simp [wbE, hl])]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · simp only [wbE_wI, embWb_in X hi (wI_in _), wI_sub]
    unfold wbE; rw [dif_pos hi]; rfl
  · simp only [embWb_out_left X hi]
    unfold wbE; rw [dif_neg hi]
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg (fun h : i = wI k r j => hi (h ▸ wI_in j)), zero_mul]

theorem embWb_mul (X Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r (X * Y) = embWb k r X * embWb k r Y := by
  ext i j
  rw [mul_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [sum_wb (f := fun l => embWb k r X i l * embWb k r Y l j)
        (by intro l hl; show embWb k r X i l * embWb k r Y l j = 0; rw [embWb_out_right X hl, if_neg (fun h : i = l => hl (h ▸ hi)), zero_mul])]
      simp only [embWb_in _ hi hj, embWb_in _ hi (wI_in _), embWb_in _ (wI_in _) hj, wI_sub, mul_apply]
    · simp only [embWb_out_right _ hj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [embWb_out_left _ hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem embWb_one : embWb k r (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) = 1 := by
  ext i j
  rw [one_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [embWb_in _ hi hj, one_apply]
      congr 1; apply propext; constructor
      · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
      · rintro rfl; rfl
    · rw [embWb_out_right _ hj]
  · rw [embWb_out_left _ hi]

theorem Hpk_mulVec_wbE (u : Fin (k + 1) → ℂ) : Hpk k r *ᵥ wbE k r u = wbE k r (Hb k *ᵥ u) := by
  funext i
  rw [Hpk_mono]
  simp only [mulVec, dotProduct, mono, of_apply, ite_mul, zero_mul]
  simp only [eq_sg_iff (i := i), Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [sg_val_in hi]
    unfold wbE et Hb; rw [dif_pos hi, dif_pos hi, if_pos hi, mulVec_diagonal]
    congr 1; congr 1; apply propext; constructor
    · intro h; apply Fin.ext; simp; omega
    · intro h; have := congrArg Fin.val h; simp at this; omega
  · have h2 := sg_out (k := k) (r := r) hi
    unfold wbE; rw [dif_neg h2, dif_neg hi, mul_zero]

theorem herm_wbE (u v : Fin (k + 1) → ℂ) : herm (Hpk k r) (wbE k r u) (wbE k r v) = herm (Hb k) u v := by
  unfold herm
  rw [Hpk_mulVec_wbE]
  simp only [dotProduct, Pi.star_apply]
  rw [sum_wb (f := fun l => star (wbE k r v l) * wbE k r (Hb k *ᵥ u) l) (by intro l hl; simp [wbE, hl])]
  simp only [wbE_wI]

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
