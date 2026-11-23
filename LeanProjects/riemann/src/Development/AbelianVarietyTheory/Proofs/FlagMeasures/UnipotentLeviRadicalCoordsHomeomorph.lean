import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NCoord

variable {k r : ℕ}

private theorem eI_val_flag_measures (a : Fin r) : (eI k r a).val = a.val := by
  simp [eI]

private theorem wI_val_flag_measures (j : Fin (k + 1)) : (wI k r j).val = r + j.val := by
  simp [wI]

private theorem esI_val_flag_measures (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := by
  simp [esI]

theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ ∃ a, i = esI k r a := by
  obtain ⟨n, hn⟩ := i
  by_cases h1 : n < r
  · left
    exact ⟨⟨n, h1⟩, Fin.ext (by rw [eI_val_flag_measures])⟩
  · right
    by_cases h2 : n ≤ r + k
    · left
      exact ⟨⟨n - r, by omega⟩, Fin.ext (by rw [wI_val_flag_measures]; simp only; omega)⟩
    · right
      exact ⟨⟨2 * r + k - n, by omega⟩, Fin.ext (by rw [esI_val_flag_measures]; simp only; omega)⟩

theorem sum_three (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = ∑ a, f (eI k r a) + ∑ j, f (wI k r j) + ∑ a, f (esI k r a) := by
  let e : Fin r ⊕ Fin (k + 1) ⊕ Fin r → Fin (2 * r + k + 1) :=
    Sum.elim (eI k r) (Sum.elim (wI k r) (esI k r))
  have hbij : Function.Bijective e := by
    constructor
    · rintro (a | a | a) (b | b | b) h <;>
        simp only [e, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, eI_val_flag_measures, wI_val_flag_measures, esI_val_flag_measures,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
        (have := a.2; have := b.2; omega)
    · intro i
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr (Sum.inl a), rfl⟩
      · exact ⟨Sum.inr (Sum.inr a), rfl⟩
  rw [← hbij.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  rfl

theorem H_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [mulVec, dotProduct]
  rw [sum_three]
  simp [Rad.H_ee, Rad.H_ew, Rad.H_es]

theorem H_es (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [mulVec, dotProduct]
  rw [sum_three]
  simp [Rad.H_se, Rad.H_sw, Rad.H_ss]

theorem H_w (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = (Hb k *ᵥ fun l => v (wI k r l)) j := by
  simp only [mulVec, dotProduct]
  rw [sum_three]
  simp [Rad.H_we, Rad.H_ww, Rad.H_ws, Hb, Rad.sg, Matrix.diagonal_apply, ite_mul]

theorem herm_three (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w =
    ∑ a, star (w (eI k r a)) * v (esI k r a) + herm (Hb k) (fun l => v (wI k r l)) (fun l => w (wI k r l)) +
      ∑ a, star (w (esI k r a)) * v (eI k r a) := by
  simp only [herm, dotProduct, Pi.star_apply]
  rw [sum_three]
  simp only [H_e, H_w, H_es]

theorem herm_col {g : Mat k r} (hg : g ∈ GG k r) (i j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (fun l => g l j) (fun l => g l i) = Hpk k r i j := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  conv_rhs => rw [← h]
  simp only [herm, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem col_eq (g : Mat k r) (i j : Fin (2 * r + k + 1)) : (g *ᵥ bvec j) i = g i j := by
  simp only [bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp

theorem herm_b_star (v w : Fin (k + 1) → ℂ) : star (herm (Hb k) v w) = herm (Hb k) w v := by
  simp only [Rad.herm_Hb, star_sum, star_mul', star_star, Rad.star_sg]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def Bof (p : Mat k r) : Fin r → Fin (k + 1) → ℂ := fun b j => p (wI k r j) (esI k r b)

def Sof (p : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  p (eI k r a) (esI k r b) + herm (Hb k) (Bof p b) (Bof p a) / 2

theorem Bof_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Bof (pEl k r B S) = B := by
  funext b j
  simp only [Bof, Rad.pEl_ws]

theorem Sof_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Sof (pEl k r B S) = S := by
  funext a b
  simp only [Sof, Bof_pEl, Rad.pEl_es, sub_add_cancel]

private theorem herm_Hpk_bvec_eq_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec x) = (Hpk k r *ᵥ v) x := by
  simp only [herm, bvec, dotProduct, Pi.star_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem rad_eq {p : Mat k r} (hp : p ∈ Nset k r) (he : ∀ a i, p i (eI k r a) = if i = eI k r a then 1 else 0) :
    (Sof p)ᴴ = -Sof p ∧ p = pEl k r (Bof p) (Sof p) := by
  obtain ⟨hU, -, hmid⟩ := hp
  have hU' : p ∈ GG k r := hU
  have hcolE : ∀ a, (fun l => p l (eI k r a)) = bvec (eI k r a) := by
    intro a; funext l; rw [he]; simp [bvec, Pi.single_apply]
  have hw : ∀ i j : Fin (k + 1), p (wI k r i) (wI k r j) = if i = j then 1 else 0 := by
    intro i j
    rw [hmid _ _ (by rw [wI_val_flag_measures]; omega) (by rw [wI_val_flag_measures]; have := j.2; omega) (by rw [wI_val_flag_measures]; omega)]
    simp only [Rad.wI_inj]
  have hsw : ∀ (a : Fin r) (j : Fin (k + 1)), p (esI k r a) (wI k r j) = 0 := by
    intro a j
    rw [hmid _ _ (by rw [wI_val_flag_measures]; omega) (by rw [wI_val_flag_measures]; have := j.2; omega)
      (by rw [esI_val_flag_measures]; have := a.2; omega), if_neg (Rad.esI_ne_wI _ _)]
  have hss : ∀ a b : Fin r, p (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
    intro a b
    have h := herm_col hU' (eI k r a) (esI k r b)
    rw [hcolE, herm_Hpk_bvec_eq_mulVec_apply, H_e, Rad.H_es] at h
    exact h
  have hst01 : ∀ c a : Fin r, star (if c = a then (1 : ℂ) else 0) = if c = a then 1 else 0 := by
    intro c a; split_ifs <;> simp
  have hmidw : ∀ j : Fin (k + 1), (fun l => p (wI k r l) (wI k r j)) = bvec j := by
    intro j; funext l; rw [hw]; simp [bvec, Pi.single_apply]
  have hew : ∀ (b : Fin r) (j : Fin (k + 1)),
      p (eI k r b) (wI k r j) = -(star (Bof p b j) * Rad.sg k j) := by
    intro b j
    have h := herm_col hU' (wI k r j) (esI k r b)
    rw [herm_three, Rad.H_ws, hmidw, ← herm_b_star, Rad.herm_bvec] at h
    simp only [hss, hsw, star_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have h2 := congrArg star h
    simp only [star_add, star_mul', star_star, Rad.star_sg, star_zero] at h2
    simp only [Bof]
    linear_combination h2
  have hrel : ∀ a b : Fin r, star (p (eI k r b) (esI k r a)) + herm (Hb k) (Bof p b) (Bof p a)
      + p (eI k r a) (esI k r b) = 0 := by
    intro a b
    have h := herm_col hU' (esI k r a) (esI k r b)
    rw [herm_three, Rad.H_ss] at h
    simp only [hss, hst01, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  refine ⟨?_, ?_⟩
  · ext a b
    have h := hrel a b
    have hs := herm_b_star (Bof p a) (Bof p b)
    simp only [conjTranspose_apply, Matrix.neg_apply, Sof, star_add, star_div₀, hs]
    have h2 : star (2 : ℂ) = 2 := by simp
    rw [h2]
    linear_combination h
  · ext i j
    rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [he, Rad.pEl_ee]; simp only [Rad.eI_inj]
    · rw [hew, Rad.pEl_ew]
    · rw [Rad.pEl_es]; simp only [Sof]; ring
    · rw [he, Rad.pEl_we, if_neg (Rad.wI_ne_eI _ _)]
    · rw [hw, Rad.pEl_ww]
    · rw [Rad.pEl_ws]; rfl
    · rw [he, Rad.pEl_se, if_neg (Rad.esI_ne_eI _ _)]
    · rw [hsw, Rad.pEl_sw]
    · rw [hss, Rad.pEl_ss]

def xOf (n : Mat k r) : UT r → ℂ := fun p => n (eI k r p.1.1) (eI k r p.1.2)

def qOf (p : Mat k r) : PPar k r := (Bof p, fun x => Sof p x.1.1 x.1.2, fun a => (Sof p a a).im)

def cOf (n : Mat k r) : (UT r → ℂ) × PPar k r := (xOf n, qOf (uEmb k r (upper (xOf n))⁻¹ * n))

theorem qOf_pOf (q : PPar k r) : qOf (pOf k r q) = q := by
  obtain ⟨B, s, t⟩ := q
  refine Prod.ext (Bof_pEl B _) (Prod.ext ?_ ?_)
  · funext x
    show Sof (pEl k r B (skewM s t)) x.1.1 x.1.2 = s x
    rw [Sof_pEl]
    simp only [skewM, dif_pos x.2]
  · funext a
    show (Sof (pEl k r B (skewM s t)) a a).im = t a
    rw [Sof_pEl]
    simp [skewM]

theorem uEmb_col (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) : uEmb k r u (eI k r a) (eI k r b) = u a b := by
  have h : (eI k r a).val < r ∧ (eI k r b).val < r := by
    rw [eI_val_flag_measures, eI_val_flag_measures]; exact ⟨a.2, b.2⟩
  simp only [uEmb, dif_pos h]
  all_goals rfl

private theorem upper_blockTriangular (x : UT r → ℂ) : (upper x).BlockTriangular id := by
  intro a b hab
  have hab' : b < a := hab
  simp only [upper, dif_neg (not_lt.mpr hab'.le), if_neg (ne_of_gt hab')]

private theorem det_upper_eq_one (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (upper_blockTriangular x)]
  refine Finset.prod_eq_one fun a _ => ?_
  simp [upper]

private theorem exists_upper_eq_inv_upper (x : UT r → ℂ) : ∃ y : UT r → ℂ, (upper x)⁻¹ = upper y := by
  have hU : IsUnit (upper x).det := by rw [det_upper_eq_one]; exact isUnit_one
  let _ := (upper x).invertibleOfIsUnitDet hU
  have ht := Matrix.blockTriangular_inv_of_blockTriangular (upper_blockTriangular x)
  have hd : ∀ a, (upper x)⁻¹ a a = 1 := by
    intro a
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul (upper x) hU) a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · have hdiag : upper x a a = 1 := by simp [upper]
      rw [hdiag, mul_one, Matrix.one_apply_eq] at h
      exact h
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hlt
      · rw [ht hlt, zero_mul]
      · rw [upper_blockTriangular x hlt, mul_zero]
    · simp
  refine ⟨fun p => (upper x)⁻¹ p.1.1 p.1.2, ?_⟩
  ext a b
  show (upper x)⁻¹ a b = (if h : a < b then (upper x)⁻¹ a b else if a = b then 1 else 0)
  split_ifs with h1 h2
  · rfl
  · subst h2; exact hd a
  · exact ht (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))

theorem uEmb_inv_mul (x : UT r → ℂ) : uEmb k r (upper x)⁻¹ * uEmb k r (upper x) = 1 ∧
    uEmb k r (upper x) * uEmb k r (upper x)⁻¹ = 1 ∧ uEmb k r (upper x)⁻¹ ∈ Nset k r := by
  have hU : IsUnit (upper x).det := by rw [det_upper_eq_one]; exact isUnit_one
  obtain ⟨y, hy⟩ := exists_upper_eq_inv_upper x
  refine ⟨?_, ?_, ?_⟩
  · rw [← UEmb.uEmb_mul, Matrix.nonsing_inv_mul _ hU, UEmb.uEmb_one]
  · rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]
  · rw [hy]; exact UEmb.upper_mem y

private theorem pEl_apply_eI (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (b : Fin r)
    (c : Fin (2 * r + k + 1)) : pEl k r B S c (eI k r b) = if c = eI k r b then 1 else 0 := by
  rcases idx_cases c with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · simp only [Rad.pEl_ee, Rad.eI_inj]
  · rw [Rad.pEl_we, if_neg (Rad.wI_ne_eI _ _)]
  · rw [Rad.pEl_se, if_neg (Rad.esI_ne_eI _ _)]

theorem cOf_coord (q : (UT r → ℂ) × PPar k r) : cOf (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  obtain ⟨s, p⟩ := q
  have hx : xOf (uEmb k r (upper s) * pOf k r p) = s := by
    funext x
    simp only [xOf, pOf, Matrix.mul_apply, pEl_apply_eI, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, uEmb_col]
    simp only [upper, dif_pos x.2]
  simp only [cOf]
  rw [hx, ← Matrix.mul_assoc, (uEmb_inv_mul s).1, Matrix.one_mul, qOf_pOf]

private theorem uEmb_apply_eI_eq_zero_of_le (u : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) (i : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) : uEmb k r u i (eI k r b) = 0 := by
  have hb := b.2
  have h1 : ¬ (i.val < r ∧ (eI k r b).val < r) := by rw [eI_val_flag_measures]; omega
  have h2 : ¬ (r + k < i.val ∧ r + k < (eI k r b).val) := by rw [eI_val_flag_measures]; omega
  have h3 : i ≠ eI k r b := by intro h; rw [h, eI_val_flag_measures] at hi; omega
  simp only [uEmb, dif_neg h1, dif_neg h2, if_neg h3]

theorem col_e {n : Mat k r} (hn : n ∈ Nset k r) (b : Fin r) :
    n *ᵥ bvec (eI k r b) = uEmb k r (upper (xOf n)) *ᵥ bvec (eI k r b) := by
  funext i
  rw [col_eq, col_eq]
  obtain ⟨-, h1, -⟩ := hn
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [uEmb_col]
    by_cases hab : a < b
    · simp only [upper, dif_pos hab, xOf]
    · have hba : b.val ≤ a.val := Fin.not_lt.mp hab
      rw [h1 b (eI k r a) (by rw [eI_val_flag_measures]; exact hba)]
      simp only [upper, dif_neg hab, Rad.eI_inj]
  · rw [h1 b _ (by rw [wI_val_flag_measures]; have := b.2; omega), if_neg (Rad.wI_ne_eI _ _),
      uEmb_apply_eI_eq_zero_of_le _ _ _ (by rw [wI_val_flag_measures]; omega)]
  · rw [h1 b _ (by rw [esI_val_flag_measures]; have := b.2; have := a.2; omega), if_neg (Rad.esI_ne_eI _ _),
      uEmb_apply_eI_eq_zero_of_le _ _ _ (by rw [esI_val_flag_measures]; have := a.2; omega)]

private theorem mul_mem_Nset {a b : Mat k r} (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) :
    a * b ∈ Nset k r := by
  obtain ⟨ha0, ha1, ha2⟩ := ha
  obtain ⟨hb0, hb1, hb2⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    have ha0' : aᴴ * Hpk k r * a = Hpk k r := ha0
    have hb0' : bᴴ * Hpk k r * b = Hpk k r := hb0
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha0', hb0']
  · intro c i hci
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]
    · rw [hb1 c _ (by rw [eI_val_flag_measures]), if_pos rfl, mul_one]
      exact ha1 c i hci
    · intro l _ hl
      by_cases hlc : c.val ≤ l.val
      · rw [hb1 c l hlc, if_neg hl, mul_zero]
      · have hlr : l.val < r := by have := c.2; omega
        have hle : eI k r ⟨l.val, hlr⟩ = l := Fin.ext (eI_val_flag_measures _)
        have hx := ha1 ⟨l.val, hlr⟩ i (by show l.val ≤ i.val; omega)
        rw [hle] at hx
        rw [hx, if_neg (by intro h; rw [h] at hci; omega), zero_mul]
    · simp
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hb2 j j hj1 hj2 hj1, if_pos rfl, mul_one]
      exact ha2 i j hj1 hj2 hi
    · intro l _ hl
      by_cases hlr : r ≤ l.val
      · rw [hb2 l j hj1 hj2 hlr, if_neg hl, mul_zero]
      · have hlr' : l.val < r := by omega
        have hle : eI k r ⟨l.val, hlr'⟩ = l := Fin.ext (eI_val_flag_measures _)
        have hx := ha1 ⟨l.val, hlr'⟩ i (by show l.val ≤ i.val; omega)
        rw [hle] at hx
        rw [hx, if_neg (by intro h; rw [h] at hi; omega), zero_mul]
    · simp

theorem exists_coord {n : Mat k r} (hn : n ∈ Nset k r) :
    ∃ q : (UT r → ℂ) × PPar k r, uEmb k r (upper q.1) * pOf k r q.2 = n := by
  obtain ⟨hVU, hUV, hV⟩ := uEmb_inv_mul (k := k) (xOf n)
  have hpN : uEmb k r (upper (xOf n))⁻¹ * n ∈ Nset k r := mul_mem_Nset hV hn
  have he : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)),
      (uEmb k r (upper (xOf n))⁻¹ * n) i (eI k r a) = if i = eI k r a then 1 else 0 := by
    intro a i
    have h2 : (uEmb k r (upper (xOf n))⁻¹ * n) *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
      rw [← Matrix.mulVec_mulVec, col_e hn, Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]
    have h3 := congrFun h2 i
    rw [col_eq] at h3
    rw [h3]
    simp [bvec, Pi.single_apply]
  obtain ⟨hS, hpe⟩ := rad_eq hpN he
  obtain ⟨st, hst, -⟩ := Rad.skewM_unique _ hS
  refine ⟨(xOf n, (Bof (uEmb k r (upper (xOf n))⁻¹ * n), st.1, st.2)), ?_⟩
  show uEmb k r (upper (xOf n)) * pEl k r (Bof (uEmb k r (upper (xOf n))⁻¹ * n)) (skewM st.1 st.2) = n
  rw [← hst, ← hpe, ← Matrix.mul_assoc, hUV, Matrix.one_mul]

theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a < b
  · simp only [upper, dif_pos h]
    exact continuous_apply _
  · simp only [upper, dif_neg h]
    exact continuous_const

theorem det_upper (x : UT r → ℂ) : (upper x).det = 1 := by
  exact det_upper_eq_one x

theorem cont_upper_inv (r : ℕ) : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
  have h : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
    funext x
    rw [Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]
  rw [h]
  exact (cont_upper r).matrix_adjugate

private theorem continuous_uEmb_of_continuous_inv {X : Type*} [TopologicalSpace X] (k r : ℕ) {f : X → Matrix (Fin r) (Fin r) ℂ}
    (hf : Continuous f) (hf' : Continuous fun x => (f x)⁻¹) : Continuous fun x => uEmb k r (f x) := by
  refine continuous_matrix fun i j => ?_
  by_cases h1 : i.val < r ∧ j.val < r
  · simp only [uEmb, dif_pos h1]
    exact hf.matrix_elem _ _
  by_cases h2 : r + k < i.val ∧ r + k < j.val
  · simp only [uEmb, dif_neg h1, dif_pos h2]
    exact (hf'.matrix_elem _ _).star
  · simp only [uEmb, dif_neg h1, dif_neg h2]
    exact continuous_const

theorem cont_uEmb (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x) := by
  exact continuous_uEmb_of_continuous_inv k r (cont_upper r) (cont_upper_inv r)

theorem cont_uEmb_inv (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x)⁻¹ := by
  refine continuous_uEmb_of_continuous_inv k r (cont_upper_inv r) ?_
  have h : (fun x : UT r → ℂ => ((upper x)⁻¹)⁻¹) = upper := by
    funext x
    exact Matrix.nonsing_inv_nonsing_inv _ (by rw [det_upper]; exact isUnit_one)
  rw [h]
  exact cont_upper r

private theorem continuous_skewM_apply {X : Type*} [TopologicalSpace X] {s : X → UT r → ℂ} {t : X → Fin r → ℝ}
    (hs : Continuous s) (ht : Continuous t) (a b : Fin r) : Continuous fun x => skewM (s x) (t x) a b := by
  by_cases h1 : a < b
  · simp only [skewM, dif_pos h1]
    exact (continuous_apply _).comp hs
  by_cases h2 : b < a
  · simp only [skewM, dif_neg h1, dif_pos h2]
    exact ((continuous_apply _).comp hs).star.neg
  · simp only [skewM, dif_neg h1, dif_neg h2]
    exact (Complex.continuous_ofReal.comp ((continuous_apply a).comp ht)).mul continuous_const

private theorem continuous_herm_Hb {X : Type*} [TopologicalSpace X] {f g : X → Fin (k + 1) → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => herm (Hb k) (f x) (g x) := by
  simp only [Rad.herm_Hb]
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp hg).star.mul (continuous_const.mul ((continuous_apply j).comp hf))

theorem cont_pOf (k r : ℕ) : Continuous (pOf k r) := by
  refine continuous_matrix fun i j => ?_
  have hB : ∀ a, Continuous fun q : PPar k r => q.1 a := fun a => (continuous_apply a).comp continuous_fst
  have hs : Continuous fun q : PPar k r => q.2.1 := continuous_fst.comp continuous_snd
  have ht : Continuous fun q : PPar k r => q.2.2 := continuous_snd.comp continuous_snd
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
  simp only [pOf, Rad.pEl_ee, Rad.pEl_ew, Rad.pEl_es, Rad.pEl_we, Rad.pEl_ww, Rad.pEl_ws,
    Rad.pEl_se, Rad.pEl_sw, Rad.pEl_ss]
  all_goals first
    | exact continuous_const
    | exact (((continuous_apply b).comp (hB a)).star.mul continuous_const).neg
    | exact (continuous_skewM_apply hs ht a b).sub ((continuous_herm_Hb (hB b) (hB a)).div_const 2)
    | exact (continuous_apply a).comp (hB b)

theorem cont_qOf (k r : ℕ) : Continuous (qOf : Mat k r → PPar k r) := by
  have hB : Continuous fun p : Mat k r => Bof p := by
    refine continuous_pi fun b => continuous_pi fun j => ?_
    simp only [Bof]
    exact continuous_id.matrix_elem _ _
  have hS : ∀ a b, Continuous fun p : Mat k r => Sof p a b := by
    intro a b
    simp only [Sof]
    exact (continuous_id.matrix_elem _ _).add
      ((continuous_herm_Hb ((continuous_apply b).comp hB) ((continuous_apply a).comp hB)).div_const 2)
  exact hB.prodMk ((continuous_pi fun x => hS _ _).prodMk
    (continuous_pi fun a => Complex.continuous_im.comp (hS a a)))

theorem cont_cOf (k r : ℕ) : Continuous (cOf : Mat k r → _) := by
  have hx : Continuous fun n : Mat k r => xOf n := by
    refine continuous_pi fun p => ?_
    simp only [xOf]
    exact continuous_id.matrix_elem _ _
  show Continuous fun n : Mat k r => (xOf n, qOf (uEmb k r (upper (xOf n))⁻¹ * n))
  exact hx.prodMk ((cont_qOf k r).comp (((cont_uEmb_inv k r).comp hx).mul continuous_id))

private theorem pOf_mem_Nset (q : PPar k r) : pOf k r q ∈ Nset k r :=
  (((Rad.radical k r).1 q.1 (skewM q.2.1 q.2.2)).2.2.2 (Rad.skewM_skew _ _)).1

theorem coord_homeo : ∀ k r : ℕ, Set.BijOn (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) Set.univ (Nset k r) ∧ Continuous (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) ∧ ∃ c : Mat k r → (UT r → ℂ) × PPar k r, Continuous c ∧ ∀ q : (UT r → ℂ) × PPar k r, c (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  intro k r
  refine ⟨⟨fun q _ => ?_, fun q _ q' _ h => ?_, fun n hn => ?_⟩, ?_, cOf, cont_cOf k r, cOf_coord⟩
  · exact mul_mem_Nset (UEmb.upper_mem q.1) (pOf_mem_Nset q.2)
  · calc q = cOf (uEmb k r (upper q.1) * pOf k r q.2) := (cOf_coord q).symm
      _ = cOf (uEmb k r (upper q'.1) * pOf k r q'.2) := congrArg cOf h
      _ = q' := cOf_coord q'
  · obtain ⟨q, hq⟩ := exists_coord hn
    exact ⟨q, Set.mem_univ _, hq⟩
  · exact ((cont_uEmb k r).comp continuous_fst).mul ((cont_pOf k r).comp continuous_snd)

end GlobalTheory.Amp.NCoord
