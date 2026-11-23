import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.HkConjTranspose

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem lf_sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (hkSig k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := rfl

theorem lf_eI_val (k r : ℕ) (a : Fin r) : (eI k r a).val = a.val := rfl

theorem lf_esI_val (k r : ℕ) (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

theorem lf_sig_eI (k r : ℕ) (a : Fin r) : hkSig k r (eI k r a) = esI k r a := by
  apply Fin.ext
  rw [lf_sig_val, lf_esI_val, lf_eI_val]
  have h := a.isLt
  rw [if_neg (by omega)]

theorem lf_eps_eI (k r : ℕ) (a : Fin r) : hkEps k r (eI k r a) = 1 := by
  have h := a.isLt
  unfold hkEps
  rw [if_neg (by rw [lf_eI_val]; omega)]

theorem lf_H_eI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if q = esI k r a then 1 else 0 := by
  rw [hk_apply, lf_sig_eI, lf_eps_eI]

theorem lf_Hmul (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (t p : Fin (2 * r + k + 1)) : (Hpk k r * g) t p = hkEps k r t * g (hkSig k r t) p := by
  rw [Matrix.mul_apply]
  simp [hk_apply, ite_mul]

theorem lf_unit_entry (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : inUH (Hpk k r) g) (b p : Fin (2 * r + k + 1)) :
    ∑ t, star (g t b) * (hkEps k r t * g (hkSig k r t) p) = Hpk k r b p := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrFun (congrFun h b) p
  rw [Matrix.mul_assoc, Matrix.mul_apply] at h2
  rw [← h2]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [lf_Hmul, Matrix.conjTranspose_apply]

theorem lf_col_of_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {j : Fin n} {v : Fin n → ℂ}
    (h : M *ᵥ bvec j = v) (t : Fin n) : M t j = v t := by
  rw [← h]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem lf_bvec_apply {n : ℕ} (j t : Fin n) : bvec j t = if t = j then 1 else 0 := by
  unfold bvec
  exact Pi.single_apply j 1 t

theorem lf_inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext t p
  rw [lf_Hmul, hk_apply, hk_sig_sig, hk_eps_sig, Matrix.one_apply]
  by_cases htp : p = t
  · subst htp
    rw [if_pos rfl, if_pos rfl]
    unfold hkEps
    split_ifs <;> norm_num
  · rw [if_neg htp, if_neg (Ne.symm htp), mul_zero]

theorem lf_det_ne_zero (k r : ℕ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : inUH (Hpk k r) g) : g.det ≠ 0 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hdH : (Hpk k r).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (hpk_sq_lemma k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  intro h0
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, h0, mul_zero] at h1
  exact hdH h1.symm

theorem lf_UW_row (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    h (esI k r a) p = if p = esI k r a then 1 else 0 := by
  obtain ⟨hU, hv, -⟩ := hh
  have hcol : ∀ t, h t (eI k r a) = if t = eI k r a then 1 else 0 := fun t => by
    rw [lf_col_of_mulVec (hv a).1 t, lf_bvec_apply]
  have h2 := lf_unit_entry k r h (show inUH (Hpk k r) h from hU) (eI k r a) p
  rw [lf_H_eI] at h2
  rw [← h2, Finset.sum_eq_single (eI k r a)]
  · rw [hcol, if_pos rfl, star_one, one_mul, lf_eps_eI, one_mul, lf_sig_eI]
  · intro t _ ht
    rw [hcol, if_neg ht, star_zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_UW_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (a : Fin r) (t : Fin (2 * r + k + 1)) :
    h t (eI k r a) = if t = eI k r a then 1 else 0 := by
  exact (lf_col_of_mulVec (hh.2.1 a).1 t).trans (lf_bvec_apply _ _)

theorem lf_sig_small (k r : ℕ) (t : Fin (2 * r + k + 1)) (ht : t.val < r) :
    hkSig k r t = esI k r ⟨t.val, ht⟩ := by
  apply Fin.ext
  rw [lf_sig_val, lf_esI_val]
  rw [if_neg (by omega)]

theorem lf_N_rowStar (k r : ℕ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.Nset k r) : ∀ (b : ℕ) (hb : b < r) (p : Fin (2 * r + k + 1)), p.val ≤ 2 * r + k - b →
      m (esI k r ⟨b, hb⟩) p = if p = esI k r ⟨b, hb⟩ then 1 else 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro hb p hp
  have hU : inUH (Hpk k r) m := hm.1
  have hcol := hm.2.1 ⟨b, hb⟩
  have h2 := lf_unit_entry k r m hU (eI k r ⟨b, hb⟩) p
  rw [lf_H_eI] at h2
  rw [← h2, Finset.sum_eq_single (eI k r ⟨b, hb⟩)]
  · rw [hcol (eI k r ⟨b, hb⟩) (lf_eI_val k r ⟨b, hb⟩).ge, if_pos rfl, star_one, one_mul, lf_eps_eI,
      one_mul, lf_sig_eI]
  · intro t _ ht
    by_cases htb : b ≤ t.val
    · rw [hcol t htb, if_neg ht, star_zero, zero_mul]
    · push_neg at htb
      have htr : t.val < r := by omega
      rw [lf_sig_small k r t htr, ih t.val htb htr p (by omega), if_neg, mul_zero, mul_zero]
      intro hpe
      have h3 : p.val = 2 * r + k - t.val := by rw [hpe, lf_esI_val]
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_S_rowStar (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : j.val ≤ 2 * r + k - a.val) :
    s (esI k r a) j = if j = esI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
  · rw [lf_UW_row k r z hh a, if_pos rfl, one_mul]
    exact lf_N_rowStar k r hm a.val a.isLt j hj
  · intro t _ ht
    rw [lf_UW_row k r z hh a, if_neg ht, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem subset_row_star : SsetRowStar := by
  unfold SsetRowStar
  intro k r z s hs a j hj
  have ha := a.isLt
  have hjl := j.isLt
  apply lf_S_rowStar k r z s hs a j
  by_contra hlt
  push_neg at hlt
  have hb : 2 * r + k - j.val < a.val := by omega
  apply hj ⟨2 * r + k - j.val, by omega⟩ hb
  apply Fin.ext
  rw [lf_esI_val]
  show j.val = 2 * r + k - (2 * r + k - j.val)
  omega

theorem subset_upper_hessenberg : SsetUH := by
  unfold SsetUH
  intro k r z s hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact lf_inUH_mul hh.1 hm.1

theorem lf_S_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    s i (eI k r a) = if i = eI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
  · rw [hm.2.1 a (eI k r a) (lf_eI_val k r a).ge, if_pos rfl, mul_one, lf_UW_col k r z hh a i]
  · intro t _ ht
    by_cases hat : a.val ≤ t.val
    · rw [hm.2.1 a t hat, if_neg ht, mul_zero]
    · push_neg at hat
      have htr : t.val < r := by have := a.isLt; omega
      have ht' : t = eI k r ⟨t.val, htr⟩ := Fin.ext (lf_eI_val k r ⟨t.val, htr⟩).symm
      rw [ht', lf_UW_col k r z hh ⟨t.val, htr⟩ i, if_neg, zero_mul]
      intro hie
      have h3 := congrArg Fin.val hie
      rw [lf_eI_val] at h3
      simp only at h3
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_triInv (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : M⁻¹ * M = 1)
    (hU : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → M i (eI k r a) = if i = eI k r a then 1 else 0) :
    ∀ (a : ℕ) (ha : a < r) (i : Fin (2 * r + k + 1)), a ≤ i.val →
      M⁻¹ i (eI k r ⟨a, ha⟩) = if i = eI k r ⟨a, ha⟩ then 1 else 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha i hi
  have h1 := congrFun (congrFun hM i) (eI k r ⟨a, ha⟩)
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [Finset.sum_eq_single (eI k r ⟨a, ha⟩)] at h1
  · rw [hU ⟨a, ha⟩ (eI k r ⟨a, ha⟩) (lf_eI_val k r ⟨a, ha⟩).ge, if_pos rfl, mul_one] at h1
    exact h1
  · intro t _ ht
    by_cases hat : a ≤ t.val
    · rw [hU ⟨a, ha⟩ t hat, if_neg ht, mul_zero]
    · push_neg at hat
      have htr : t.val < r := by omega
      have ht' : t = eI k r ⟨t.val, htr⟩ := Fin.ext (lf_eI_val k r ⟨t.val, htr⟩).symm
      rw [ht', ih t.val hat htr i (by omega), if_neg, zero_mul]
      intro hie
      have h3 := congrArg Fin.val hie
      rw [lf_eI_val] at h3
      simp only at h3
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_S_invCol (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    s⁻¹ i (eI k r a) = if i = eI k r a then 1 else 0 := by
  have hUH : inUH (Hpk k r) s := subset_upper_hessenberg k r z s hs
  have hdet : IsUnit s.det := isUnit_iff_ne_zero.mpr (lf_det_ne_zero k r hUH)
  exact lf_triInv k r s (Matrix.nonsing_inv_mul s hdet) (fun b i' hb => lf_S_col k r z s hs b i' hb)
    a.val a.isLt i hi

theorem subset_inverse_column : SsetInvCol := by
  unfold SsetInvCol
  intro k r z s hs a i hi
  apply lf_S_invCol k r z s hs a i
  by_contra hlt
  push_neg at hlt
  have ha := a.isLt
  exact hi ⟨i.val, by omega⟩ hlt (Fin.ext (lf_eI_val k r ⟨i.val, by omega⟩).symm)

end AAInvW
