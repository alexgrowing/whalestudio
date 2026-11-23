import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace RvB

variable {k r : ℕ}

theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; have := a.isLt; have := b.isLt; omega

theorem eI_inj {a b : Fin r} (h : eI k r a = eI k r b) : a = b := by
  simp only [eI, Fin.ext_iff] at h; exact Fin.ext h

theorem esI_inj {a b : Fin r} (h : esI k r a = esI k r b) : a = b := by
  simp only [esI, Fin.ext_iff] at h; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)

theorem w1_mulVec_bvec_eI (a : Fin r) (c : ℂ) : Q.w1 k r a c *ᵥ bvec (eI k r a) = c • bvec (esI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_e, Formalism.FourierDecayAlt.P.Qx3.dd_e]
  split_ifs <;> simp

theorem w1_mulVec_bvec_esI (a : Fin r) (c : ℂ) : Q.w1 k r a c *ᵥ bvec (esI k r a) = (star c)⁻¹ • bvec (eI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]
  split_ifs <;> simp

theorem w1_mulVec_eq_self_of_eI_esI_eq_zero (b : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (h1 : v (eI k r b) = 0)
    (h2 : v (esI k r b) = 0) : Q.w1 k r b c *ᵥ v = v := by
  funext p
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Formalism.FourierDecayAlt.P.Qx3.sw k b p)]
  · rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_pos (Formalism.FourierDecayAlt.P.Qx3.sw_sw b p).symm]
    rcases Formalism.FourierDecayAlt.P.Qx3.tri b p with h | h | ⟨h1', h2'⟩
    · subst h; rw [Formalism.FourierDecayAlt.P.Qx3.sw_e, h2, h1, mul_zero]
    · subst h; rw [Formalism.FourierDecayAlt.P.Qx3.sw_es, h1, h2, mul_zero]
    · rw [Formalism.FourierDecayAlt.P.Qx3.sw_o b h1' h2', Formalism.FourierDecayAlt.P.Qx3.dd_o b c h1' h2', one_mul]
  · intro q _ hq
    have : p ≠ Formalism.FourierDecayAlt.P.Qx3.sw k b q := fun h => hq (by rw [h, Formalism.FourierDecayAlt.P.Qx3.sw_sw])
    rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem wl_fixv (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b, v (eI k r b) = 0 ∧ v (esI k r b) = 0) : (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, w1_mulVec_eq_self_of_eI_esI_eq_zero b _ v (hv b).1 (hv b).2]

theorem wl_e (c : Fin r → ℂ) (L : List (Fin r)) (hL : L.Nodup) (a : Fin r) :
    (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec (eI k r a) =
      if a ∈ L then c a • bvec (esI k r a) else bvec (eI k r a) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]
    by_cases hab : a = b
    · subst hab
      rw [if_neg hL.1, w1_mulVec_bvec_eI, if_pos List.mem_cons_self]
    · have hmem : (a ∈ b :: L) ↔ a ∈ L := by simp [hab]
      by_cases h1 : a ∈ L
      · rw [if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]
      · rw [if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]

theorem wl_es (c : Fin r → ℂ) (L : List (Fin r)) (hL : L.Nodup) (a : Fin r) :
    (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec (esI k r a) =
      if a ∈ L then (star (c a))⁻¹ • bvec (eI k r a) else bvec (esI k r a) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]
    by_cases hab : a = b
    · subst hab
      rw [if_neg hL.1, w1_mulVec_bvec_esI, if_pos List.mem_cons_self]
    · have hmem : (a ∈ b :: L) ↔ a ∈ L := by simp [hab]
      by_cases h1 : a ∈ L
      · rw [if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]
      · rw [if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]

theorem wc_list (c : Fin r → ℂ) : Q.wCell k r (Fin.last r) c =
    (((List.finRange r).filter fun a => a.val < (Fin.last r).val).map fun a => Q.w1 k r a (c a)).prod := rfl

theorem wc_nodup : ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val).Nodup :=
  (List.nodup_finRange r).filter _

theorem wc_mem (a : Fin r) : a ∈ ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val) := by
  rw [List.mem_filter]; exact ⟨List.mem_finRange a, by simp [a.isLt]⟩

theorem W_e (c : Fin r → ℂ) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ bvec (eI k r a) = c a • bvec (esI k r a) := by
  rw [wc_list, wl_e c _ wc_nodup, if_pos (wc_mem a)]

theorem W_es (c : Fin r → ℂ) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a) := by
  rw [wc_list, wl_es c _ wc_nodup, if_pos (wc_mem a)]

theorem W_fix (c : Fin r → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ b, v (eI k r b) = 0 ∧ v (esI k r b) = 0) :
    Q.wCell k r (Fin.last r) c *ᵥ v = v := by
  rw [wc_list, wl_fixv c _ v hv]

theorem herm_uh {W : Q.Mx k r} (hW : W ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (W *ᵥ x) (W *ᵥ y) = herm (Hpk k r) x y := by
  have hW' : Wᴴ * Hpk k r * W = Hpk k r := hW
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW']

theorem herm_smul_right (x w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) x (s • w) = star s * herm (Hpk k r) x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec q) (bvec p) = Hpk k r p q := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

section what₂

variable {c : Fin r → ℂ} {g : Q.Mx k r}

theorem row_e (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec q) (bvec (eI k r a)) =
      if q = eI k r a then c a else 0 := by
  have hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r) :=
    (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1
  have hca : star (c a) ≠ 0 := star_ne_zero.2 (hc a)
  have he : bvec (eI k r a) = Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a)) := by
    rw [Matrix.mulVec_smul, W_es, smul_smul, mul_inv_cancel₀ hca, one_smul]
  have hges : g *ᵥ bvec (esI k r a) = bvec (esI k r a) := (hg.2 a (by simp [a.isLt])).2
  rw [← Matrix.mulVec_mulVec, he, herm_uh hW, herm_smul_right, star_star, ← hges, herm_uh hg.1, herm_bvec,
    Formalism.FourierDecayAlt.P.Qx3.hpk_row_es]
  split_ifs <;> simp

theorem herm_wCell_last_mul_mulVec_eq_of_inWb (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ v) z = herm (Hpk k r) (g *ᵥ v) z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r) :=
    (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1
  have hzf : Q.wCell k r (Fin.last r) c *ᵥ z = z := W_fix c z fun b =>
    ⟨hz _ (Or.inl (by simp [eI])), hz _ (Or.inr (by simp [esI]; have := b.isLt; omega))⟩
  conv_lhs => rw [← hzf]
  rw [← Matrix.mulVec_mulVec, herm_uh hW]

theorem row_z_e (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin r) :
    herm (Hpk k r) (g *ᵥ bvec (eI k r a)) z = 0 ∧ herm (Hpk k r) (g *ᵥ bvec (esI k r a)) z = 0 := by
  obtain ⟨h1, h2⟩ := hg.2 a (by simp [a.isLt])
  have hz1 : z (esI k r a) = 0 := hz _ (Or.inr (by simp [esI]; have := a.isLt; omega))
  have hz2 : z (eI k r a) = 0 := hz _ (Or.inl (by simp [eI]))
  rw [h1, h2]
  constructor
  · simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Formalism.FourierDecayAlt.P.Qx3.hpk_col_e]
    split_ifs with h
    · subst h; simp [hz1]
    · simp
  · simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Formalism.FourierDecayAlt.P.Qx3.hpk_col_es]
    split_ifs with h
    · subst h; simp [hz2]
    · simp

end what₂

section dets

def Arow (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.of fun p q =>
    if h : p.val < r then (if q = eI k r ⟨p.val, h⟩ then c ⟨p.val, h⟩ else 0)
    else if h2 : p.val = r then (if q = wI k r t then 1 else 0)
    else if q = J ⟨p.val - r - 1, by have := p.isLt; omega⟩ then 1 else 0

theorem det_prop {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {p p' : Fin m} (h : p ≠ p') (l : ℂ) (hA : A p = l • A p') :
    A.det = 0 := by
  have e : A = A.updateRow p (l • A p') := by rw [← hA, Matrix.updateRow_eq_self]
  rw [e, Matrix.det_updateRow_smul,
    Matrix.det_zero_of_row_eq h (by rw [Matrix.updateRow_self, Matrix.updateRow_ne h.symm]), mul_zero]

theorem det_updateRow_sum' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (v : ι → Fin m → ℂ) :
    (A.updateRow i (∑ t ∈ s, a t • v t)).det = ∑ t ∈ s, a t * (A.updateRow i (v t)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]

theorem colsV_strictMono (t : Fin (k + 1)) : StrictMono (colsV k r t) := by
  intro i j h
  simp only [colsV, Fin.lt_def] at h ⊢
  split_ifs <;> omega

theorem colsV_mem_jSet (t : Fin (k + 1)) : colsV k r t ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert colsV_strictMono (k := k) (r := r) t

theorem prod_d (c : Fin r → ℂ) :
    ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) = ∏ a : Fin r, c a := by
  let f : ℕ → ℂ := fun i => if h : i < r then c ⟨i, h⟩ else 1
  have h1 : ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) =
      ∏ i ∈ Finset.range (2 * r + k + 1), f i := Fin.prod_univ_eq_prod_range f _
  have h2 : ∏ a : Fin r, c a = ∏ i ∈ Finset.range r, f i := by
    rw [← Fin.prod_univ_eq_prod_range f r]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [f, a.isLt]
  rw [h1, h2, ← Finset.prod_range_mul_prod_Ico f (show r ≤ 2 * r + k + 1 by omega)]
  rw [Finset.prod_eq_one (s := Finset.Ico r (2 * r + k + 1)) (fun i hi => by
    simp only [Finset.mem_Ico] at hi; simp [f, show ¬ i < r by omega]), mul_one]

theorem arow_zero (c : Fin r → ℂ) (h0 : 0 < k + 1) :
    Arow c (colsV k r ⟨0, h0⟩) ⟨0, h0⟩ = Matrix.diagonal fun p => if h : p.val < r then c ⟨p.val, h⟩ else 1 := by
  ext p q
  simp only [Arow, Matrix.of_apply, Matrix.diagonal_apply, colsV, eI, wI, Fin.ext_iff, Nat.not_lt_zero,
    if_false]
  split_ifs <;> first | rfl | omega

end dets

section dets2

theorem arow_succ (c : Fin r → ℂ) (t : ℕ) (ht : t + 1 < k + 1) :
    Arow c (colsV k r ⟨t + 1, ht⟩) ⟨t + 1, ht⟩ =
      (Arow c (colsV k r ⟨t, by omega⟩) ⟨t, by omega⟩).submatrix
        (Equiv.swap (⟨r, by omega⟩ : Fin (2 * r + k + 1)) ⟨r + 1 + t, by omega⟩) id := by
  ext p q
  simp only [Matrix.submatrix_apply, id, Equiv.swap_apply_def]
  by_cases h1 : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
  · subst h1
    simp only [if_true]
    simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · by_cases h2 : p = (⟨r + 1 + t, by omega⟩ : Fin (2 * r + k + 1))
    · subst h2
      simp only [if_neg h1, if_true]
      simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    · simp only [if_neg h1, if_neg h2]
      have h1' : p.val ≠ r := fun h => h1 (Fin.ext h)
      have h2' : p.val ≠ r + 1 + t := fun h => h2 (Fin.ext h)
      simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem det_arow_colsV (c : Fin r → ℂ) :
    ∀ (t : ℕ) (ht : t < k + 1), (Arow c (colsV k r ⟨t, ht⟩) ⟨t, ht⟩).det = (-1) ^ t * ∏ a, c a
  | 0, ht => by rw [arow_zero c ht, Matrix.det_diagonal, prod_d, pow_zero, one_mul]
  | t + 1, ht => by
    rw [arow_succ c t ht, Matrix.det_permute, Equiv.Perm.sign_swap (by simp only [ne_eq, Fin.ext_iff]; omega),
      det_arow_colsV c t (by omega), pow_succ]
    push_cast
    ring

end dets2

section dets3

theorem det_arow_ne (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) (t : Fin (k + 1))
    (hne : J ≠ colsV k r t) : (Arow c J t).det = 0 := by
  by_cases hA : ∃ j : Fin (r + k), (J j).val < r
  · obtain ⟨j, hj⟩ := hA
    have hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j := fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))
    refine det_prop (p := ⟨(J j).val, by omega⟩) (p' := ⟨r + 1 + j.val, by omega⟩)
      (by simp only [ne_eq, Fin.ext_iff]; omega) (c ⟨(J j).val, hj⟩) ?_
    funext q
    simp only [Arow, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, dif_pos hj,
      dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj]
    have : eI k r ⟨(J j).val, hj⟩ = J j := Fin.ext rfl
    rw [this]
    split_ifs <;> simp
  · push Not at hA
    by_cases hB : ∃ j, J j = wI k r t
    · obtain ⟨j, hj⟩ := hB
      have hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j := fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))
      refine Matrix.det_zero_of_row_eq (i := ⟨r, by omega⟩) (j := ⟨r + 1 + j.val, by omega⟩)
        (by simp only [ne_eq, Fin.ext_iff]; omega) ?_
      funext q
      simp only [Arow, Matrix.of_apply, dif_neg (show ¬ (r < r) by omega),
        dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj, hj]
      exact dif_pos trivial
    · push Not at hB
      exfalso
      apply hne
      have hsub : Finset.image J Finset.univ ⊆ Finset.image (colsV k r t) Finset.univ := by
        intro q hq
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
        have h1 := hA j
        have h2 : (J j).val ≠ r + t.val := fun h => hB j (Fin.ext (by simp [wI, h]))
        have hlt := (J j).isLt
        refine Finset.mem_image.2 ⟨⟨if (J j).val < r + t.val then (J j).val - r else (J j).val - r - 1, by
          have := t.isLt; split_ifs <;> omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp only [colsV]
        split_ifs <;> omega
      have hcard : (Finset.image (colsV k r t) Finset.univ).card ≤ (Finset.image J Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hJ.injective,
          Finset.card_image_of_injective _ (colsV_strictMono t).injective]
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have hrange : Set.range J = Set.range (colsV k r t) := by
        have := congrArg (fun s : Finset (Fin (2 * r + k + 1)) => (s : Set (Fin (2 * r + k + 1)))) heq
        simpa [Finset.coe_image] using this
      exact (hJ.range_inj (colsV_strictMono t)).1 hrange

end dets3

section cell

variable {c : Fin r → ℂ} {g : Q.Mx k r}

theorem arow_update (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩ (bvec (wI k r t)) = Arow c J t := by
  ext p q
  rw [Matrix.updateRow_apply]
  by_cases hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
  · rw [if_pos hp]
    subst hp
    simp only [Arow, Matrix.of_apply, dif_neg (lt_irrefl r), bvec, Pi.single_apply]
    rw [dif_pos trivial]
  · rw [if_neg hp]
    have hp' : p.val ≠ r := fun h => hp (Fin.ext h)
    simp only [Arow, Matrix.of_apply, dif_neg hp']

theorem yrow_sum (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (fun q => herm (Hpk k r) (g *ᵥ bvec q) z) =
      ∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t) := by
  funext q
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hq : r ≤ q.val ∧ q.val ≤ r + k
  · obtain ⟨t0, rfl⟩ : ∃ t0 : Fin (k + 1), q = wI k r t0 :=
      ⟨⟨q.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩
    rw [Finset.sum_eq_single t0 (fun t _ ht => if_neg (fun h => ht (by
      simp only [wI, Fin.ext_iff] at h; exact Fin.ext (by omega)))) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · rw [Finset.sum_eq_zero (fun t _ => if_neg (fun h => hq (by
      rw [h]; simp only [wI]; have := t.isLt; omega)))]
    by_cases h1 : q.val < r
    · have : q = eI k r ⟨q.val, h1⟩ := Fin.ext rfl
      rw [this]; exact (row_z_e hg hz _).1
    · have hq2 : r + k < q.val := by omega
      have : q = esI k r ⟨2 * r + k - q.val, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp only [esI]; have := q.isLt; omega)
      rw [this]; exact (row_z_e hg hz _).2

theorem alJ_cell (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    alJ k r z (Q.wCell k r (Fin.last r) c * g) J =
      ∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z * (Arow c J t).det := by
  have hM : (Matrix.of fun p q => rowV k r z (Q.wCell k r (Fin.last r) c * g) J p q) =
      (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩
        (∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t)) := by
    rw [← yrow_sum hg hz]
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
    · rw [if_pos hp]
      subst hp
      simp only [Matrix.of_apply, rowV, dif_neg (lt_irrefl r)]
      rw [dif_pos trivial]
      exact herm_wCell_last_mul_mulVec_eq_of_inWb hc hz (bvec q)
    · rw [if_neg hp]
      have hp' : p.val ≠ r := fun h => hp (Fin.ext h)
      simp only [Matrix.of_apply, rowV, Arow]
      by_cases h1 : p.val < r
      · rw [dif_pos h1, dif_pos h1, row_e hc hg]
      · rw [dif_neg h1, dif_neg h1, dif_neg hp', dif_neg hp']
  unfold alJ
  rw [hM, det_updateRow_sum' _ _ Finset.univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [arow_update]

theorem alJ_val (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) :
    alJ k r z (Q.wCell k r (Fin.last r) c * g) J =
      ∑ s : Fin (k + 1), (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a)) *
        (if J = colsV k r s then 1 else 0) := by
  rw [alJ_cell hc hg hz]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : J = colsV k r s
  · subst h
    have hd : (Arow c (colsV k r s) s).det = (-1) ^ (s : ℕ) * ∏ a, c a := det_arow_colsV c s.val s.isLt
    rw [hd, if_pos rfl, mul_one]
  · rw [det_arow_ne c J hJ s h, if_neg h, mul_zero, mul_zero]

end cell

end RvB

theorem mirror_residue_beta_holds : JDRvBeta := by
  intro k r
  refine ⟨1, one_ne_zero, ?_⟩
  intro E _ _ z z' Y f hz c hc g hg
  have hsm : ∀ J ∈ jSetR k r, StrictMono J := fun J hJ => by
    classical
    simpa [jSetR] using hJ
  have hL : rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
      ∑ t : Fin (k + 1), ∑ s : Fin (k + 1),
        (((-1 : ℂ) ^ (t : ℕ) * z' (wI k r t)) *
            (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a))) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g) := by
    unfold rvhatOp
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun J hJ => by rw [RvB.alJ_val hc hg hz J (hsm J hJ)]]
    simp_rw [Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single (colsV k r s)]
    · rw [if_pos rfl, mul_one]
    · intro J _ hJ
      rw [if_neg hJ, mul_zero, mul_zero, zero_smul]
    · intro h
      exact absurd (RvB.colsV_mem_jSet s) h
  have hR : NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g) =
      ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
        (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g) := by
    show (∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
        (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) *
            herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g)) = _
    simp only [RvB.herm_wCell_last_mul_mulVec_eq_of_inWb hc hz]
  rw [hL, hR, Finset.smul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]
  congr 1
  rw [pow_add]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP
