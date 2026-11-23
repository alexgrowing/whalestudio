import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCharA

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem unit_of_frame {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : γᴴ * Hb k * γ = Hb k) : IsUnit γ.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h1
  have hHb : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => by split_ifs <;> norm_num)
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  exact hHb h1.symm

private theorem wI_val_eq_add (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

private theorem wI_val_mem_block (j : Fin (k + 1)) : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
  have := j.isLt
  rw [wI_val_eq_add]
  constructor <;> omega

private theorem wI_val_sub_eq (j : Fin (k + 1)) :
    (⟨(wI k r j).val - r, by rw [wI_val_eq_add]; omega⟩ : Fin (k + 1)) = j := by
  exact Fin.ext (by simp [wI_val_eq_add])

private theorem sum_eq_sum_wI_of_zero_off_block {f : Fin (2 * r + k + 1) → ℂ}
    (hf : ∀ i : Fin (2 * r + k + 1), ¬ (r ≤ i.val ∧ i.val ≤ r + k) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  have hinj : Function.Injective (wI k r) := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    rw [wI_val_eq_add, wI_val_eq_add] at this
    omega
  symm
  refine Fintype.sum_of_injective (wI k r) hinj (fun j => f (wI k r j)) f (fun i hi => hf i ?_) (fun j => rfl)
  rintro ⟨h1, h2⟩
  exact hi ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI_val_eq_add, Fin.val_mk]; omega)⟩

private theorem embWb_apply_of_mem_block (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : r ≤ i.val ∧ i.val ≤ r + k) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    embWb k r X i j = X ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ := by
  simp only [embWb]
  rw [dif_pos ⟨hi, hj⟩]

private theorem embWb_apply_of_left_not_mem_block (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) : embWb k r X i j = if i = j then 1 else 0 := by
  simp only [embWb]
  rw [dif_neg (show ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) from fun h => hi h.1)]
  by_cases h : i = j
  · rw [if_pos (show i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) from ⟨h, hi⟩), if_pos h]
  · rw [if_neg (show ¬ (i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) from fun h' => h h'.1), if_neg h]

private theorem embWb_apply_of_right_not_mem_block (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) : embWb k r X i j = if i = j then 1 else 0 := by
  simp only [embWb]
  rw [dif_neg (show ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) from fun h => hj h.2)]
  by_cases h : i = j
  · rw [if_pos (show i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) from ⟨h, by rw [h]; exact hj⟩), if_pos h]
  · rw [if_neg (show ¬ (i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) from fun h' => h h'.1), if_neg h]

private theorem embWb_mul' (X Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r (X * Y) = embWb k r X * embWb k r Y := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [embWb_apply_of_mem_block _ hi hj, sum_eq_sum_wI_of_zero_off_block (f := fun l => embWb k r X i l * embWb k r Y l j)
        (fun l hl => by
          show embWb k r X i l * embWb k r Y l j = 0
          rw [embWb_apply_of_right_not_mem_block X hl, if_neg (fun h => hl (by rw [← h]; exact hi)), zero_mul])]
      simp only [embWb_apply_of_mem_block _ hi (wI_val_mem_block _), embWb_apply_of_mem_block _ (wI_val_mem_block _) hj, wI_val_sub_eq, Matrix.mul_apply]
    · rw [Finset.sum_eq_single j]
      · simp [embWb_apply_of_right_not_mem_block X hj, embWb_apply_of_right_not_mem_block Y hj, embWb_apply_of_right_not_mem_block (X * Y) hj]
      · intro l _ hl
        rw [embWb_apply_of_right_not_mem_block Y hj, if_neg hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
  · rw [Finset.sum_eq_single i]
    · simp [embWb_apply_of_left_not_mem_block X hi, embWb_apply_of_left_not_mem_block Y hi, embWb_apply_of_left_not_mem_block (X * Y) hi]
    · intro l _ hl
      rw [embWb_apply_of_left_not_mem_block X hi, if_neg (Ne.symm hl), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

private theorem embWb_one' : embWb k r (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [embWb_apply_of_mem_block _ hi hj, Matrix.one_apply]
      simp only [Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | omega
    · rw [embWb_apply_of_right_not_mem_block _ hj]
  · rw [embWb_apply_of_left_not_mem_block _ hi]

theorem unit_embWb {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) :
    IsUnit (embWb k r γ).det := by
  have h1 : embWb k r γ * embWb k r γ⁻¹ = 1 := by
    rw [← embWb_mul', Matrix.mul_nonsing_inv _ hγ, embWb_one']
  exact Matrix.isUnit_det_of_right_inverse h1

theorem not_isW_eI (a : Fin r) : ¬ isW k r (eI k r a) := by
  intro h
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : r ≤ (eI k r a).val := h.1
  omega

theorem cStd_conj_re (w : ℂ) : (cStd * conj w).re = -(cStd * w).re := by
  first
  | (simp [cStd, Complex.mul_re, Complex.mul_im]; ring)
  | simp [cStd, Complex.mul_re, Complex.mul_im]
  | (simp [cStd, Complex.mul_re, Complex.mul_im]; linarith)

section
variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det)
include hE

private theorem embWb_apply_eq_ite_of_left_index_not_isW {i : Fin (2 * r + k + 1)} (hi : ¬ isW k r i) (j : Fin (2 * r + k + 1)) :
    embWb k r γ i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := hi
  simp only [embWb]
  rw [dif_neg (show ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) from fun h => hi' h.1)]
  by_cases h : i = j
  · rw [if_pos (show i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) from ⟨h, hi'⟩), if_pos h]
  · rw [if_neg (show ¬ (i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) from fun h' => h h'.1), if_neg h]

private theorem embWb_apply_eq_ite_of_right_index_not_isW {j : Fin (2 * r + k + 1)} (hj : ¬ isW k r j) (i : Fin (2 * r + k + 1)) :
    embWb k r γ i j = if i = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k) := hj
  simp only [embWb]
  rw [dif_neg (show ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) from fun h => hj' h.2)]
  by_cases h : i = j
  · rw [if_pos (show i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) from ⟨h, by rw [h]; exact hj'⟩), if_pos h]
  · rw [if_neg (show ¬ (i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) from fun h' => h h'.1), if_neg h]

private theorem mul_apply_of_left_index_eq_single {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {i : Fin (2 * r + k + 1)}
    (hA : ∀ l, A i l = if i = l then 1 else 0) (j : Fin (2 * r + k + 1)) : (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA i, if_pos rfl, one_mul]
  · intro l _ hl
    rw [hA l, if_neg (Ne.symm hl), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem mul_apply_of_right_col_eq_single {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {j : Fin (2 * r + k + 1)}
    (hB : ∀ l, B l j = if l = j then 1 else 0) (i : Fin (2 * r + k + 1)) : (A * B) i j = A i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hB j, if_pos rfl, mul_one]
  · intro l _ hl
    rw [hB l, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem embWb_inv_apply_of_left_index_not_isW {i : Fin (2 * r + k + 1)} (hi : ¬ isW k r i) (j : Fin (2 * r + k + 1)) :
    (embWb k r γ)⁻¹ i j = if i = j then 1 else 0 := by
  have h1 : (embWb k r γ * (embWb k r γ)⁻¹) i j = if i = j then 1 else 0 := by
    rw [Matrix.mul_nonsing_inv _ hE, Matrix.one_apply]
  rwa [mul_apply_of_left_index_eq_single hE (embWb_apply_eq_ite_of_left_index_not_isW hE hi)] at h1

private theorem embWb_inv_apply_of_right_index_not_isW {j : Fin (2 * r + k + 1)} (hj : ¬ isW k r j) (i : Fin (2 * r + k + 1)) :
    (embWb k r γ)⁻¹ i j = if i = j then 1 else 0 := by
  have h1 : ((embWb k r γ)⁻¹ * embWb k r γ) i j = if i = j then 1 else 0 := by
    rw [Matrix.nonsing_inv_mul _ hE, Matrix.one_apply]
  rwa [mul_apply_of_right_col_eq_single hE (embWb_apply_eq_ite_of_right_index_not_isW hE hj)] at h1

private theorem embWb_mulVec_apply_of_not_isW {i : Fin (2 * r + k + 1)} (hi : ¬ isW k r i) (w : Fin (2 * r + k + 1) → ℂ) :
    (embWb k r γ *ᵥ w) i = w i := by
  show ∑ j, embWb k r γ i j * w j = w i
  rw [Finset.sum_eq_single i]
  · rw [embWb_apply_eq_ite_of_left_index_not_isW hE hi i, if_pos rfl, one_mul]
  · intro l _ hl
    rw [embWb_apply_eq_ite_of_left_index_not_isW hE hi l, if_neg (Ne.symm hl), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem embWb_inv_apply_offW (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (hi : ¬ isW k r i) :
    ((embWb k r γ)⁻¹ *ᵥ v) i = v i := by
  show ∑ j, (embWb k r γ)⁻¹ i j * v j = v i
  rw [Finset.sum_eq_single i]
  · rw [embWb_inv_apply_of_left_index_not_isW hE hi i, if_pos rfl, one_mul]
  · intro l _ hl
    rw [embWb_inv_apply_of_left_index_not_isW hE hi l, if_neg (Ne.symm hl), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cc_apply_offW (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (hi : ¬ isW k r i) :
    cc γ v i = conj (v i) := by
  simp only [cc]
  rw [embWb_mulVec_apply_of_not_isW hE hi]
  show conj (((embWb k r γ)⁻¹ *ᵥ v) i) = conj (v i)
  rw [embWb_inv_apply_offW hE v i hi]

theorem frame_conjugation_fixes_vector (z : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z)
    (hfr : embWb k r γ *ᵥ bvec (wI k r (Fin.last k)) = (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) :
    cc γ z = z := by
  have hs : Real.sqrt (Tz k r z) ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  have hz : z = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • (embWb k r γ *ᵥ bvec (wI k r (Fin.last k))) := by
    rw [hfr, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one, one_smul]
  have hinv : (embWb k r γ)⁻¹ *ᵥ z = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) := by
    conv_lhs => rw [hz]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  simp only [cc]
  rw [hinv]
  conv_rhs => rw [hz]
  rw [← Matrix.mulVec_smul]
  congr 1
  funext l
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  congr 1
  simp only [bvec, Pi.single_apply]
  split_ifs <;> simp

theorem gbar_apply_off (g : Mat k r) (i j : Fin (2 * r + k + 1)) (hi : ¬ isW k r i) (hj : ¬ isW k r j) :
    gbar k r γ g i j = conj (g i j) := by
  simp only [gbar]
  rw [mul_apply_of_right_col_eq_single hE (embWb_inv_apply_of_right_index_not_isW hE hj), mul_apply_of_left_index_eq_single hE (embWb_apply_eq_ite_of_left_index_not_isW hE hi), Matrix.map_apply,
    mul_apply_of_right_col_eq_single hE (embWb_apply_eq_ite_of_right_index_not_isW hE hj), mul_apply_of_left_index_eq_single hE (embWb_inv_apply_of_left_index_not_isW hE hi)]

theorem gbar_mulVec_off (g : Mat k r) (v : Fin (2 * r + k + 1) → ℂ) (hv : cc γ v = v)
    (i : Fin (2 * r + k + 1)) (hi : ¬ isW k r i) : (gbar k r γ g *ᵥ v) i = conj ((g *ᵥ v) i) := by
  have hu : (fun l => conj (((embWb k r γ)⁻¹ *ᵥ v) l)) = (embWb k r γ)⁻¹ *ᵥ v := by
    have h1 : embWb k r γ *ᵥ (fun l => conj (((embWb k r γ)⁻¹ *ᵥ v) l)) = v := hv
    conv_rhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  have hconj : ∀ (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      Y.map (starRingEnd ℂ) *ᵥ (fun l => conj (w l)) = fun l => conj ((Y *ᵥ w) l) := by
    intro Y w
    funext l
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hY : ((embWb k r γ)⁻¹ * g * embWb k r γ) *ᵥ ((embWb k r γ)⁻¹ *ᵥ v) = (embWb k r γ)⁻¹ *ᵥ (g *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc ((embWb k r γ)⁻¹ * g) (embWb k r γ),
      Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
  have key : gbar k r γ g *ᵥ v = cc γ (g *ᵥ v) := by
    simp only [gbar, cc]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu, hconj, hY]
  rw [key]
  exact cc_apply_offW hE (g *ᵥ v) i hi

theorem ell_gbar (z : Fin (2 * r + k + 1) → ℂ) (hz : cc γ z = z) (g : Mat k r) :
    ell k r z (gbar k r γ g) = conj (ell k r z g) := by
  unfold ell
  rw [map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · exact gbar_apply_off hE g _ _ (not_isW_eI a) (not_isW_eI _)
  · exact gbar_mulVec_off hE g z hz _ (not_isW_eI a)

end

theorem N_inv_col (m n : Mat k r) (hm : m ∈ Nset k r) (hnm : n * m = 1) :
    ∀ (j : ℕ) (hj : j < r) (i : Fin (2 * r + k + 1)), j ≤ i.val →
      n i (eI k r ⟨j, hj⟩) = if i = eI k r ⟨j, hj⟩ then 1 else 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hji
    have hm2 := hm.2.1
    have h1 : (n * m) i (eI k r ⟨j, hj⟩) = if i = eI k r ⟨j, hj⟩ then 1 else 0 := by
      rw [hnm, Matrix.one_apply]
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r ⟨j, hj⟩)] at h1
    · rw [hm2 ⟨j, hj⟩ (eI k r ⟨j, hj⟩) (le_refl _), if_pos rfl, mul_one] at h1
      exact h1
    · intro l _ hl
      by_cases hlj : j ≤ l.val
      · rw [hm2 ⟨j, hj⟩ l hlj, if_neg hl, mul_zero]
      · have hl' : l.val < r := by omega
        have hel : eI k r ⟨l.val, hl'⟩ = l := Fin.ext rfl
        have hil := ih l.val (by omega) hl' i (by omega)
        rw [hel, if_neg (show ¬ i = l from fun h => by subst h; omega)] at hil
        rw [hil, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem mulVec_apply_eq_sum' (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

theorem N_inv_vec (m n : Mat k r) (hm : m ∈ Nset k r) (hnm : n * m = 1) (a : Fin r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv0 : ∀ p : Fin (2 * r + k + 1), p.val ≤ a.val → v p = 0)
    (hmv : ∀ p : Fin (2 * r + k + 1), a.val < p.val → (m *ᵥ v) p = v p) :
    (n *ᵥ v) (eI k r a) = -((m *ᵥ v) (eI k r a)) := by
  have hrow : ∀ p : Fin (2 * r + k + 1), p.val ≤ a.val → n (eI k r a) p = if p = eI k r a then 1 else 0 := by
    intro p hp
    have hpr : p.val < r := by have := a.isLt; omega
    have hel : eI k r ⟨p.val, hpr⟩ = p := Fin.ext rfl
    have hc := N_inv_col m n hm hnm p.val hpr (eI k r a) hp
    rw [hel] at hc
    rw [hc]
    by_cases h : p = eI k r a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hsplit : ∀ p, n (eI k r a) p * (m *ᵥ v) p =
      n (eI k r a) p * v p + (if p = eI k r a then (m *ᵥ v) p else 0) := by
    intro p
    by_cases hp : a.val < p.val
    · rw [hmv p hp, if_neg (show ¬ p = eI k r a from fun h => by subst h; exact lt_irrefl _ hp), add_zero]
    · have hp' : p.val ≤ a.val := by omega
      rw [hv0 p hp', mul_zero, zero_add, hrow p hp']
      split_ifs <;> simp
  have hnmv : (n *ᵥ (m *ᵥ v)) (eI k r a) = 0 := by
    rw [Matrix.mulVec_mulVec, hnm, Matrix.one_mulVec]
    exact hv0 (eI k r a) (le_refl _)
  have hexp : (n *ᵥ (m *ᵥ v)) (eI k r a) = (n *ᵥ v) (eI k r a) + (m *ᵥ v) (eI k r a) := by
    rw [mulVec_apply_eq_sum' n (m *ᵥ v), mulVec_apply_eq_sum' n v, Finset.sum_congr rfl (fun p _ => hsplit p),
      Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [hexp] at hnmv
  linear_combination hnmv

private theorem mulVec_bvec_apply_multiplicity_one (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j i : Fin (2 * r + k + 1)) : (M *ᵥ bvec j) i = M i j := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]

theorem ell_inv_N (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (m n : Mat k r) (hm : m ∈ Nset k r)
    (hnm : n * m = 1) : ell k r z n = -ell k r z m := by
  unfold ell
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · have hv : (eI k r ⟨a.val + 1, h⟩).val = a.val + 1 := rfl
    have key := N_inv_vec m n hm hnm a (bvec (eI k r ⟨a.val + 1, h⟩)) (fun p hp => ?_) (fun p hp => ?_)
    · rw [mulVec_bvec_apply_multiplicity_one, mulVec_bvec_apply_multiplicity_one] at key
      exact key
    · simp only [bvec, Pi.single_apply]
      rw [if_neg (show ¬ p = eI k r ⟨a.val + 1, h⟩ from fun hpe => by rw [hpe] at hp; omega)]
    · rw [mulVec_bvec_apply_multiplicity_one, hm.2.1 ⟨a.val + 1, h⟩ p (show a.val + 1 ≤ p.val by omega)]
      simp only [bvec, Pi.single_apply]
  · refine N_inv_vec m n hm hnm a z (fun p hp => hz p (Or.inl (by have := a.isLt; omega))) (fun p hp => ?_)
    have hpr : r ≤ p.val := by have := a.isLt; omega
    rw [mulVec_apply_eq_sum', Finset.sum_eq_single p]
    · by_cases hpw : p.val ≤ r + k
      · rw [hm.2.2 p p hpr hpw hpr, if_pos rfl, one_mul]
      · rw [hz p (Or.inr (by omega)), mul_zero]
    · intro j _ hjp
      by_cases hjw : r ≤ j.val ∧ j.val ≤ r + k
      · rw [hm.2.2 p j hjw.1 hjw.2 hpr, if_neg (Ne.symm hjp), zero_mul]
      · rw [hz j (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr
