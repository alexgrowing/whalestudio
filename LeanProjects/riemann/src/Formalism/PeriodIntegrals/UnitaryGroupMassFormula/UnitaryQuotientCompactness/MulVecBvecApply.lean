import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

def inW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

lemma mulVec_bvec_apply (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (g *ᵥ bvec j) i = g i j := by
  simp [bvec]

lemma bvec_apply (i j : Fin (2 * r + k + 1)) : bvec j i = if i = j then 1 else 0 := by
  simp [bvec, Pi.single_apply]

lemma uw_col_out {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (j : Fin (2 * r + k + 1)) (hj : ¬ inW k r j) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨-, hfix, -⟩ := hh
  have key : h *ᵥ bvec j = bvec j := by
    unfold inW at hj
    by_cases hjr : j.val < r
    · have h1 := (hfix ⟨j.val, hjr⟩).1
      have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rwa [e] at h1
    · have ha : 2 * r + k - j.val < r := by
        have := j.isLt
        omega
      have h1 := (hfix ⟨2 * r + k - j.val, ha⟩).2
      have e : esI k r ⟨2 * r + k - j.val, ha⟩ = j := by
        apply Fin.ext
        show 2 * r + k - (2 * r + k - j.val) = j.val
        have := j.isLt
        omega
      rwa [e] at h1
  rw [← mulVec_bvec_apply h i j, key, bvec_apply]

lemma piI_not_inW {i : Fin (2 * r + k + 1)} (hi : ¬ inW k r i) : ¬ inW k r (piI k r i) := by
  unfold inW at hi ⊢
  unfold piI
  rw [if_neg hi]
  show ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k)
  have := i.isLt
  omega

private lemma Hpk_applyUnitaryQuotientCompactness (i x : Fin (2 * r + k + 1)) :
    Hpk k r i x = if x = piI k r i then (if i.val = r + k then (-1 : ℂ) else 1) else 0 := by
  have hx := x.isLt
  have hi := i.isLt
  by_cases hW : r ≤ i.val ∧ i.val ≤ r + k
  · have hp : piI k r i = i := by
      unfold piI
      exact if_pos hW
    rw [hp]
    unfold Hpk
    have n1 : ¬ (i.val < r ∧ i.val + x.val = 2 * r + k) := by omega
    rw [if_neg n1]
    by_cases hxi : x = i
    · subst hxi
      have n2 : ¬ (x.val < r ∧ x.val + x.val = 2 * r + k) := by omega
      rw [if_neg n2, if_pos ⟨hW.1, hW.2, rfl⟩, if_pos rfl]
    · have hxv : x.val ≠ i.val := fun h => hxi (Fin.ext h)
      have n2 : ¬ (x.val < r ∧ i.val + x.val = 2 * r + k) := by omega
      have n3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = x) := fun h => hxi h.2.2.symm
      rw [if_neg n2, if_neg n3, if_neg hxi]
  · have hp : piI k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold piI
      exact if_neg hW
    rw [hp]
    unfold Hpk
    have hc : ¬ (i.val = r + k) := by omega
    have n3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = x) := fun h => hW ⟨h.1, h.2.1⟩
    rw [if_neg hc]
    by_cases hxi : x.val = 2 * r + k - i.val
    · have hx' : x = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext hxi
      rw [if_pos hx']
      by_cases hir : i.val < r
      · rw [if_pos ⟨hir, by omega⟩]
      · have n1 : ¬ (i.val < r ∧ i.val + x.val = 2 * r + k) := fun h => hir h.1
        have p2 : x.val < r ∧ i.val + x.val = 2 * r + k := ⟨by omega, by omega⟩
        rw [if_neg n1, if_pos p2]
    · have hx' : ¬ x = ⟨2 * r + k - i.val, by omega⟩ := fun h => hxi (congrArg Fin.val h)
      have n1 : ¬ (i.val < r ∧ i.val + x.val = 2 * r + k) := by omega
      have n2 : ¬ (x.val < r ∧ i.val + x.val = 2 * r + k) := by omega
      rw [if_neg hx', if_neg n1, if_neg n2, if_neg n3]

private lemma piI_piI' (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  by_cases hW : r ≤ i.val ∧ i.val ≤ r + k
  · have hp : piI k r i = i := by
      unfold piI
      exact if_pos hW
    rw [hp, hp]
  · have hi := i.isLt
    have hp : piI k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold piI
      exact if_neg hW
    rw [hp]
    have hW' : ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k) := by omega
    unfold piI
    rw [if_neg hW']
    apply Fin.ext
    show 2 * r + k - (2 * r + k - i.val) = i.val
    omega

lemma uw_block {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) (hij : ¬ (inW k r i ∧ inW k r j)) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : inW k r j
  · have hi : ¬ inW k r i := fun h' => hij ⟨h', hj⟩
    have hne : i ≠ j := fun e => hi (by rw [e]; exact hj)
    rw [if_neg hne]
    have hh' := hh
    simp only [UWset, Set.mem_setOf_eq] at hh'
    have hU : hᴴ * Hpk k r * h = Hpk k r := hh'.1
    have hp := piI_not_inW hi
    have hcol : ∀ x, h x (piI k r i) = if x = piI k r i then 1 else 0 :=
      fun x => uw_col_out hh _ hp x
    have hrowp : ∀ y, (hᴴ * Hpk k r) (piI k r i) y = Hpk k r (piI k r i) y := by
      intro y
      rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]
      · rw [Matrix.conjTranspose_apply, hcol, if_pos rfl, star_one, one_mul]
      · intro x _ hx
        rw [Matrix.conjTranspose_apply, hcol, if_neg hx, star_zero, zero_mul]
      · intro hm
        exact absurd (Finset.mem_univ _) hm
    have e := congrFun (congrFun hU (piI k r i)) j
    rw [Matrix.mul_apply] at e
    simp only [hrowp] at e
    rw [Finset.sum_eq_single i] at e
    · rw [Hpk_applyUnitaryQuotientCompactness (piI k r i) i, Hpk_applyUnitaryQuotientCompactness (piI k r i) j, piI_piI', if_pos rfl,
        if_neg (Ne.symm hne)] at e
      have hc : (if (piI k r i).val = r + k then (-1 : ℂ) else 1) ≠ 0 := by
        split_ifs <;> norm_num
      exact (mul_eq_zero.mp e).resolve_left hc
    · intro y _ hy
      rw [Hpk_applyUnitaryQuotientCompactness (piI k r i) y, piI_piI', if_neg hy, zero_mul]
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · exact uw_col_out hh j hj i

lemma one_mem_UW : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp only [UWset, UH, Set.mem_setOf_eq]
  refine ⟨by simp, fun a => ⟨by simp, by simp⟩, by simp⟩

lemma mul_mem_UW {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) : a * b ∈ UWset k r z := by
  simp only [UWset, UH, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, fun i => ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha1, hb1]
  · rw [← Matrix.mulVec_mulVec, (hb2 i).1, (ha2 i).1]
  · rw [← Matrix.mulVec_mulVec, (hb2 i).2, (ha2 i).2]
  · rw [← Matrix.mulVec_mulVec, hb3, ha3]

private lemma sign_mul_sign_piI_eq_one (i : Fin (2 * r + k + 1)) :
    (if i.val = r + k then (-1 : ℂ) else 1) *
      (if (piI k r i).val = r + k then (-1 : ℂ) else 1) = 1 := by
  by_cases hW : r ≤ i.val ∧ i.val ≤ r + k
  · have hp : piI k r i = i := by
      unfold piI
      exact if_pos hW
    rw [hp]
    split_ifs <;> norm_num
  · have hi := i.isLt
    have hp : piI k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold piI
      exact if_neg hW
    rw [hp]
    have h1 : ¬ (i.val = r + k) := by omega
    have h2 : ¬ ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val = r + k) := by
      show ¬ (2 * r + k - i.val = r + k)
      omega
    rw [if_neg h1, if_neg h2, one_mul]

private lemma Hpk_mul_Hpk : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (piI k r i)]
  · rw [Hpk_applyUnitaryQuotientCompactness i (piI k r i), if_pos rfl, Hpk_applyUnitaryQuotientCompactness (piI k r i) j, piI_piI']
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, sign_mul_sign_piI_eq_one]
    · rw [if_neg (Ne.symm hij), if_neg hij, mul_zero]
  · intro x _ hx
    rw [Hpk_applyUnitaryQuotientCompactness i x, if_neg hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma inv_fix {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) : a⁻¹ *ᵥ v = v := by
  have hU' : aᴴ * Hpk k r * a = Hpk k r := hU
  have hl : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', Hpk_mul_Hpk]
  rw [Matrix.inv_eq_left_inv hl]
  calc (Hpk k r * aᴴ * Hpk k r) *ᵥ v = (Hpk k r * aᴴ * Hpk k r) *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]

lemma inv_mem_UW {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UWset k r z) : a⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have hU : aᴴ * Hpk k r * a = Hpk k r := ha1
  have hl : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Hpk_mul_Hpk]
  have hinv : a⁻¹ = Hpk k r * aᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have hr : a * a⁻¹ = 1 := by
    have hla : a⁻¹ * a = 1 := by
      rw [hinv]
      exact hl
    exact Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hla)
  refine ⟨?_, fun i => ⟨inv_fix ha1 (ha2 i).1, inv_fix ha1 (ha2 i).2⟩, inv_fix ha1 ha3⟩
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  have hrH : (a⁻¹)ᴴ * aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [hU]
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hrH, hr, Matrix.one_mul, Matrix.mul_one]

lemma uw_sub_S {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨h, hh, 1, ?_, (Matrix.mul_one h).symm⟩
  simp only [Nset, UH, Set.mem_setOf_eq]
  refine ⟨by simp, fun a i _ => ?_, fun i j _ _ _ => ?_⟩
  · rw [Matrix.one_apply]
  · rw [Matrix.one_apply]

lemma n_sub_S {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    n ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  exact ⟨1, one_mem_UW, n, hn, (Matrix.one_mul n).symm⟩

end PI.QuotSetU.UnitaryGroupMassFormula.SW
