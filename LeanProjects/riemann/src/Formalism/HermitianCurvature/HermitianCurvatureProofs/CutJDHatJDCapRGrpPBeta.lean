import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JDBeta

open Formalism.FourierDecayAlt.P.CutMP Matrix

noncomputable section

variable {k r : ℕ}

def ptv (k r : ℕ) (t : Fin (k + 1)) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if q.val < r then r + k + 1 + q.val else if q.val = r then r + t.val
    else if q.val - r - 1 < r + t.val then q.val - r - 1 else q.val - r, by
    have := q.isLt; have := t.isLt; split_ifs <;> omega⟩

theorem ptv_inj (t : Fin (k + 1)) : Function.Injective (ptv k r t) := by
  intro q₁ q₂ h
  have h' := congrArg Fin.val h
  simp only [ptv] at h'
  apply Fin.ext
  have := q₁.isLt; have := q₂.isLt
  split_ifs at h' <;> omega

def Pt (k r : ℕ) (t : Fin (k + 1)) : Equiv.Perm (Fin (2 * r + k + 1)) :=
  Equiv.ofBijective (ptv k r t) (Finite.injective_iff_bijective.1 (ptv_inj t))

theorem Pt_apply (t : Fin (k + 1)) (q : Fin (2 * r + k + 1)) : Pt k r t q = ptv k r t q := rfl

theorem Pt_succ (t : ℕ) (ht : t + 1 < k + 1) :
    Pt k r ⟨t + 1, ht⟩ = Pt k r ⟨t, by omega⟩ *
      Equiv.swap (⟨r, by omega⟩ : Fin (2 * r + k + 1)) ⟨2 * r + 1 + t, by omega⟩ := by
  ext q
  simp only [Equiv.Perm.mul_apply, Pt_apply, Equiv.swap_apply_def]
  have := q.isLt
  split_ifs with h1 h2
  · subst h1; simp only [ptv]; split_ifs <;> omega
  · subst h2; simp only [ptv]; split_ifs <;> omega
  · have e1 : q.val ≠ r := fun e => h1 (Fin.ext e)
    have e2 : q.val ≠ 2 * r + 1 + t := fun e => h2 (Fin.ext e)
    simp only [ptv]
    split_ifs <;> omega

theorem sign_Pt (t : ℕ) (ht : t < k + 1) :
    (Equiv.Perm.sign (Pt k r ⟨t, ht⟩) : ℤ) = (-1) ^ t * (Equiv.Perm.sign (Pt k r 0) : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Pt_succ t ht, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by simp [Fin.ext_iff]; omega), Units.val_mul,
      ih (by omega), pow_succ]
    simp only [Units.val_neg, Units.val_one]
    ring

theorem rowsR_val (t : Fin (k + 1)) (j : Fin (r + k)) :
    (rowsR k r t j).val = if j.val < r + t.val then j.val else j.val + 1 := rfl

theorem rowsR_strictMono (t : Fin (k + 1)) : StrictMono (rowsR k r t) := by
  intro j₁ j₂ h
  rw [Fin.lt_def, rowsR_val, rowsR_val]
  rw [Fin.lt_def] at h
  split_ifs <;> omega

theorem residue_rows_injective {t t' : Fin (k + 1)} (h : rowsR k r t = rowsR k r t') : t = t' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne (Fin.ext e) : t.val ≠ t'.val) with hl | hl
  · have := congrArg Fin.val (congrFun h ⟨r + t.val, by have := t'.isLt; omega⟩)
    simp only [rowsR_val, Fin.val_mk] at this
    split_ifs at this <;> omega
  · have := congrArg Fin.val (congrFun h ⟨r + t'.val, by have := t.isLt; omega⟩)
    simp only [rowsR_val, Fin.val_mk] at this
    split_ifs at this <;> omega

theorem rowsR_mem (t : Fin (k + 1)) : rowsR k r t ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert rowsR_strictMono t

section det

variable (z : Fin (2 * r + k + 1) → ℂ) (x : Q.Mx k r) (v : Fin r → ℂ)
  (h1 : ∀ a : Fin r, ginvH k r x *ᵥ bvec (eI k r a) = v a • bvec (esI k r a))
  (h2 : ∀ p : Fin (2 * r + k + 1), p.val < r → (ginvH k r x *ᵥ z) p = 0)
include h1

theorem colR_lt (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) (hq : q.val < r) :
    colR k r z x J q p = if p.val = r + k + 1 + q.val then v ⟨r - 1 - q.val, by omega⟩ else 0 := by
  unfold colR
  rw [dif_pos hq, h1]
  simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  simp only [esI, Fin.ext_iff]
  apply propext
  constructor <;> intro h <;> omega

omit h1 in
theorem colR_eq (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) (hq : q.val = r) :
    colR k r z x J q p = (ginvH k r x *ᵥ z) p := by
  unfold colR
  rw [dif_neg (by omega), dif_pos hq]

omit h1 in
theorem colR_gt (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) (hq : r < q.val) :
    colR k r z x J q p = if p = J ⟨q.val - r - 1, by have := q.isLt; omega⟩ then 1 else 0 := by
  unfold colR
  rw [dif_neg (by omega), dif_neg (by omega)]
  simp only [bvec, Pi.single_apply]

include h2

theorem claimA (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) (σ : Equiv.Perm (Fin (2 * r + k + 1)))
    (hσ : ∏ i, colR k r z x J i (σ i) ≠ 0) : ∃ t, J = rowsR k r t ∧ σ = Pt k r t := by
  classical
  have hne : ∀ i, colR k r z x J i (σ i) ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hσ i (Finset.mem_univ _)
  have hlt : ∀ q : Fin (2 * r + k + 1), q.val < r → (σ q).val = r + k + 1 + q.val := by
    intro q hq
    have := hne q
    rw [colR_lt z x v h1 J q _ hq] at this
    by_contra h
    exact this (if_neg h)
  have hgt : ∀ (q : Fin (2 * r + k + 1)) (hq : r < q.val), σ q = J ⟨q.val - r - 1, by have := q.isLt; omega⟩ := by
    intro q hq
    have := hne q
    rw [colR_gt z x J q _ hq] at this
    by_contra h
    exact this (if_neg h)
  have hr0 : r ≤ (σ ⟨r, by omega⟩).val := by
    by_contra h
    have := hne ⟨r, by omega⟩
    rw [colR_eq z x J _ _ rfl, h2 _ (by omega)] at this
    exact this rfl
  have hstar : ∀ (p : Fin (2 * r + k + 1)) (q : Fin (2 * r + k + 1)), r < q.val → r + k < (σ q).val → False := by
    intro p q hq hs
    have hq' : (σ q).val - r - k - 1 < r := by have := (σ q).isLt; omega
    have e := hlt ⟨(σ q).val - r - k - 1, by omega⟩ hq'
    have : σ ⟨(σ q).val - r - k - 1, by omega⟩ = σ q := Fin.ext (by simp only at e; omega)
    have := congrArg Fin.val (σ.injective this)
    simp only at this
    omega
  have hr1 : (σ ⟨r, by omega⟩).val ≤ r + k := by
    by_contra h
    have hq' : (σ ⟨r, by omega⟩).val - r - k - 1 < r := by have := (σ ⟨r, by omega⟩).isLt; omega
    have e := hlt ⟨(σ ⟨r, by omega⟩).val - r - k - 1, by omega⟩ hq'
    have : σ ⟨(σ ⟨r, by omega⟩).val - r - k - 1, by omega⟩ = σ ⟨r, by omega⟩ := Fin.ext (by simp only at e; omega)
    have := congrArg Fin.val (σ.injective this)
    simp only at this
    omega
  set t : Fin (k + 1) := ⟨(σ ⟨r, by omega⟩).val - r, by omega⟩ with ht
  have hJS : ∀ j : Fin (r + k), (J j).val ≤ r + k ∧ (J j).val ≠ r + t.val := by
    intro j
    have e := hgt ⟨r + 1 + j.val, by have := j.isLt; omega⟩ (by simp only; omega)
    have ej : (⟨(r + 1 + j.val) - r - 1, by have := j.isLt; omega⟩ : Fin (r + k)) = j := Fin.ext (by simp only; omega)
    rw [ej] at e
    rw [← e]
    constructor
    · by_contra h
      exact hstar 0 ⟨r + 1 + j.val, by have := j.isLt; omega⟩ (by show r < r + 1 + j.val; omega) (by omega)
    · intro h
      have : σ ⟨r + 1 + j.val, by have := j.isLt; omega⟩ = σ ⟨r, by omega⟩ := Fin.ext (by rw [h, ht]; simp only; omega)
      have := congrArg Fin.val (σ.injective this)
      simp only at this
      omega
  let S : Finset (Fin (2 * r + k + 1)) := Finset.univ.filter fun p => p.val ≤ r + k ∧ p.val ≠ r + t.val
  have hSimg : S = Finset.univ.image (rowsR k r t) := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1', h2'⟩
      refine ⟨⟨if p.val < r + t.val then p.val else p.val - 1, by have := t.isLt; split_ifs <;> omega⟩, ?_⟩
      apply Fin.ext
      rw [rowsR_val]
      simp only
      split_ifs <;> omega
    · rintro ⟨j, rfl⟩
      rw [rowsR_val]
      have := j.isLt
      split_ifs <;> omega
  have hcard : S.card = r + k := by
    rw [hSimg, Finset.card_image_of_injective _ (rowsR_strictMono t).injective, Finset.card_univ, Fintype.card_fin]
  have hJeq : J = rowsR k r t := by
    have e1 := Finset.orderEmbOfFin_unique hcard (f := J) (fun j => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hJS j) hJ
    have e2 := Finset.orderEmbOfFin_unique hcard (f := rowsR k r t) (fun j => by
      rw [hSimg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) (rowsR_strictMono t)
    rw [e1, e2]
  refine ⟨t, hJeq, ?_⟩
  ext q
  rw [Pt_apply]
  simp only [ptv]
  rcases lt_trichotomy q.val r with hq | hq | hq
  · rw [hlt q hq, if_pos hq]
  · have htv : t.val = (σ ⟨r, by omega⟩).val - r := by rw [ht]
    have e : q = ⟨r, by omega⟩ := Fin.ext hq
    rw [if_neg (by omega), if_pos hq, e]
    omega
  · rw [hgt q hq, hJeq, rowsR_val]
    simp only [Fin.val_mk]
    split_ifs <;> omega

end det

section det2

variable (z : Fin (2 * r + k + 1) → ℂ) (x : Q.Mx k r) (v : Fin r → ℂ)
  (h1 : ∀ a : Fin r, ginvH k r x *ᵥ bvec (eI k r a) = v a • bvec (esI k r a))
  (h2 : ∀ p : Fin (2 * r + k + 1), p.val < r → (ginvH k r x *ᵥ z) p = 0)
omit h1 in
theorem prod_rev_v : (∏ i : Fin (2 * r + k + 1), (if h : i.val < r then v ⟨r - 1 - i.val, by omega⟩ else 1)) =
    ∏ a, v a := by
  let F : ℕ → ℂ := fun i => if h : i < r then v ⟨r - 1 - i, by omega⟩ else 1
  have e1 : (∏ i : Fin (2 * r + k + 1), (if h : i.val < r then v ⟨r - 1 - i.val, by omega⟩ else 1)) =
      ∏ i ∈ Finset.range (2 * r + k + 1), F i := Fin.prod_univ_eq_prod_range F _
  rw [e1, ← Finset.prod_range_mul_prod_Ico F (show r ≤ 2 * r + k + 1 by omega)]
  rw [Finset.prod_eq_one (s := Finset.Ico r (2 * r + k + 1)) (fun i hi => by
    simp only [F]; rw [dif_neg (by simp [Finset.mem_Ico] at hi; omega)]), mul_one]
  rw [← Fin.prod_univ_eq_prod_range F r]
  rw [← Equiv.prod_comp Fin.revPerm v]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [F, dif_pos a.isLt, Fin.revPerm_apply]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

include h1 in
theorem claimB (t : Fin (k + 1)) :
    ∏ i, colR k r z x (rowsR k r t) i (Pt k r t i) = (∏ a, v a) * (ginvH k r x *ᵥ z) (wI k r t) := by
  have hf : ∀ i, colR k r z x (rowsR k r t) i (Pt k r t i) =
      (if h : i.val < r then v ⟨r - 1 - i.val, by omega⟩ else 1) *
        (if i = ⟨r, by omega⟩ then (ginvH k r x *ᵥ z) (wI k r t) else 1) := by
    intro i
    rcases lt_trichotomy i.val r with hi | hi | hi
    · rw [colR_lt z x v h1 _ i _ hi, if_pos (by rw [Pt_apply]; simp only [ptv]; rw [if_pos hi]), dif_pos hi,
        if_neg (fun e => by rw [e] at hi; simp at hi), mul_one]
    · have e : i = ⟨r, by omega⟩ := Fin.ext hi
      rw [colR_eq z x _ i _ hi, dif_neg (by omega), if_pos e, one_mul]
      congr 1
      apply Fin.ext
      rw [Pt_apply]
      simp only [ptv, wI]
      rw [if_neg (by omega), if_pos hi]
    · have hP : Pt k r t i = rowsR k r t ⟨i.val - r - 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        rw [Pt_apply, rowsR_val]
        simp only [ptv, Fin.val_mk]
        split_ifs <;> omega
      have hne : i ≠ ⟨r, by omega⟩ := fun e => by rw [e] at hi; simp at hi
      rw [colR_gt z x _ i _ hi, if_pos hP, dif_neg (by omega), if_neg hne, mul_one]
  rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib, prod_rev_v (k := k) v,
    Finset.prod_eq_single (⟨r, by omega⟩ : Fin (2 * r + k + 1)) (fun b _ hb => if_neg hb) (by simp), if_pos rfl]

include h1 h2 in
theorem det_formula (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) :
    beJ k r z x J = ∑ t : Fin (k + 1), if J = rowsR k r t then
      ((Equiv.Perm.sign (Pt k r t) : ℤ) : ℂ) * (∏ a, v a) * (ginvH k r x *ᵥ z) (wI k r t) else 0 := by
  unfold beJ
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  by_cases hex : ∃ t, J = rowsR k r t
  · obtain ⟨t₀, rfl⟩ := hex
    rw [Finset.sum_eq_single t₀ (fun t _ ht => if_neg (fun e => ht (residue_rows_injective e).symm)) (by simp), if_pos rfl]
    rw [Finset.sum_eq_single (Pt k r t₀) (fun σ _ hσ => ?_) (by simp)]
    · rw [claimB z x v h1 t₀, Units.smul_def, zsmul_eq_mul]
      ring
    · by_contra hne
      have hp : ∏ i, colR k r z x (rowsR k r t₀) i (σ i) ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      obtain ⟨t, ht, hσt⟩ := claimA z x v h1 h2 _ (rowsR_strictMono t₀) σ hp
      exact hσ (by rw [hσt, ← residue_rows_injective ht])
  · rw [Finset.sum_eq_zero (fun t _ => if_neg (fun e => hex ⟨t, e⟩))]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_contra hne
    have hp : ∏ i, colR k r z x J i (σ i) ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
    obtain ⟨t, ht, -⟩ := claimA z x v h1 h2 J hJ σ hp
    exact hex ⟨t, ht⟩

end det2

section pt

theorem hpk_mulVec_eI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have : Hpk k r (eI k r a) (esI k r a) = 1 := by
      have := a.isLt
      unfold Hpk
      simp only [eI, esI]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff] <;> omega)
    rw [this, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun e => hj (Fin.ext (by simp only [esI]; omega))
    have : Hpk k r (eI k r a) j = 0 := by
      have := a.isLt; have := j.isLt
      unfold Hpk
      simp only [eI]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff] <;> omega)
    rw [this, zero_mul]
  · simp

variable {c : Fin r → ℂ} {g : Q.Mx k r}

theorem x_glev0 (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) :
    Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)

theorem ginvH_mul (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) :
    ginvH k r (Q.wCell k r (Fin.last r) c * g) * (Q.wCell k r (Fin.last r) c * g) = 1 := by
  have hU := (x_glev0 hc hg).1
  unfold UH at hU
  simp only [Set.mem_setOf_eq] at hU
  unfold ginvH
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Hpk k r), hU, GBasic.Hpk_sq]

theorem x_esI (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    (Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a) := by
  rw [← Matrix.mulVec_mulVec, (hg.2 a (by simp)).2, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  funext i
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  unfold bigCell
  have ha := a.isLt
  rw [dif_neg (by simp [esI]; omega), dif_neg (by simp [esI]; omega)]
  by_cases hi : i = eI k r a
  · subst hi
    rw [if_pos (by simp [eI, esI]; omega), if_pos rfl]
    congr 2
    exact congrArg c (Fin.ext (by simp only [esI]; omega))
  · rw [if_neg (fun e => hi (Fin.ext (by simp [eI, esI] at e ⊢; omega))), if_neg hi]

theorem ginvH_wCell_last_mul_mulVec_bvec_eI (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    ginvH k r (Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (eI k r a) = star (c a) • bvec (esI k r a) := by
  have hca : star (c a) ≠ 0 := star_ne_zero.2 (hc a)
  have e : bvec (eI k r a) = (Q.wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) := by
    rw [Matrix.mulVec_smul, x_esI hg a, smul_smul, mul_inv_cancel₀ hca, one_smul]
  rw [e, Matrix.mulVec_mulVec, ginvH_mul hc hg, Matrix.one_mulVec]

theorem ginvH_wCell_mul_apply_eq_zero (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hg : g ∈ Q.Glev k r (Fin.last r))
    (p : Fin (2 * r + k + 1)) (hp : p.val < r) :
    (ginvH k r (Q.wCell k r (Fin.last r) c * g) *ᵥ z) p = 0 := by
  have ep : p = eI k r ⟨p.val, hp⟩ := Fin.ext rfl
  rw [ep]
  unfold ginvH
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hpk_mulVec_eI]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  have hcol : ∀ j, (Q.wCell k r (Fin.last r) c * g) j (esI k r ⟨p.val, hp⟩) =
      ((star (c ⟨p.val, hp⟩))⁻¹ • bvec (eI k r ⟨p.val, hp⟩)) j := by
    intro j
    rw [← x_esI hg]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  simp only [hcol, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have := hpk_mulVec_eI (k := k) ⟨p.val, hp⟩ z
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Finset.sum_eq_single (eI k r ⟨p.val, hp⟩) (fun b _ hb => by rw [if_neg hb, star_zero, zero_mul]) (by simp),
    if_pos rfl, this, hz (esI k r ⟨p.val, hp⟩) (Or.inr (by simp only [esI]; omega)), mul_zero]

end pt

theorem qm_cast {m m' : ℕ} (h : m = m') (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) :
    qminorOp (Q.EH k r) a b u f = qminorOp (Q.EH k r) (a ∘ Fin.cast h.symm) (b ∘ Fin.cast h.symm) u f := by
  subst h
  rfl

theorem qm_rowsN (i t : Fin (k + 1)) (u : ℂ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Q.Mx k r → E) :
    qminorOp (Q.EH k r) (rowsR k r i) (rowsR k r t) u f = qminorOp (Q.EH k r) (rowsN k r 0 i) (rowsN k r 0 t) u f := by
  have h : r + k = r - (0 : Fin (r + 1)).val + k := by simp
  have e : ∀ s : Fin (k + 1), rowsN k r 0 s = rowsR k r s ∘ Fin.cast h.symm := by
    intro s
    funext j
    apply Fin.ext
    simp only [rowsN, Function.comp_apply, rowsR_val]
    simp
    rfl
  rw [qm_cast h, e i, e t]

theorem residue_beta_holds : JDRBeta := by
  intro k r
  refine ⟨((Equiv.Perm.sign (Pt k r 0) : ℤ) : ℂ), by simp, ?_⟩
  intro E _ _ z z' Y f hz c hc g hg
  have h1 := ginvH_wCell_last_mul_mulVec_bvec_eI hc hg
  have h2 := ginvH_wCell_mul_apply_eq_zero (c := c) z hz hg
  have hinv : (Q.wCell k r (Fin.last r) c * g)⁻¹ = ginvH k r (Q.wCell k r (Fin.last r) c * g) :=
    Matrix.inv_eq_left_inv (ginvH_mul hc hg)
  unfold rhatOp NL
  rw [hinv, Finset.smul_sum]
  have hL : ∀ i : Fin (k + 1), (∑ J ∈ jSetR k r,
      (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z (Q.wCell k r (Fin.last r) c * g) J) •
        qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g)) =
      ∑ t : Fin (k + 1), (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' *
        (((Equiv.Perm.sign (Pt k r t) : ℤ) : ℂ) * (∏ a, star (c a)) *
          (ginvH k r (Q.wCell k r (Fin.last r) c * g) *ᵥ z) (wI k r t))) •
        qminorOp (Q.EH k r) (rowsR k r i) (rowsR k r t) (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g) := by
    intro i
    classical
    rw [Finset.sum_congr rfl (fun J hJ => by
      rw [det_formula z _ (fun a => star (c a)) h1 h2 J (by
        simp only [jSetR, Finset.mem_filter] at hJ; convert hJ.2)])]
    simp only [Finset.mul_sum, Finset.sum_smul, mul_ite, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq' (jSetR k r) (rowsR k r t), if_pos (rowsR_mem t)]
  rw [Finset.sum_congr rfl fun i _ => hL i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]
  have hs := sign_Pt (k := k) (r := r) t.val t.isLt
  simp only [Fin.eta] at hs
  have hp : (∏ a, star (c a)) = starRingEnd ℂ (∏ a, c a) := by
    rw [map_prod]; rfl
  rw [qm_rowsN]
  congr 1
  rw [hs, hp]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.JDBeta
