import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section dpsi

variable {k r : ℕ}

theorem hpk_col_esI (a : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r l (esI k r a) = if l.val = a.val then 1 else 0 := by
  have ha := a.isLt
  have hl := l.isLt
  unfold Hpk esI
  by_cases hla : l.val = a.val
  · rw [if_pos (by simp only [Fin.val_mk]; omega), if_pos hla]
  · rw [if_neg (by simp only [Fin.val_mk]; omega), if_neg (by simp only [Fin.val_mk]; omega),
      if_neg (by simp only [Fin.ext_iff, Fin.val_mk]; omega), if_neg hla]

theorem hpk_W_row (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w p = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2.symm)]

theorem hpk_W_col (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r p w = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2)]

theorem hpk_W_sq (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) : Hpk k r w w * Hpk k r w w = 1 := by
  unfold Hpk
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hw.1, hw.2, rfl⟩]
  split_ifs <;> norm_num

theorem herm_Hpk_bvec_eq_star_mul_diag_of_middle (z' : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    herm (Hpk k r) (bvec p) z' = star (z' p) * Hpk k r p p := by
  have hc : ∀ l, Hpk k r l p = if l = p then Hpk k r p p else 0 := fun l => hpk_W_col p l hp
  unfold herm bvec
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single p]
  · intro l _ hl
    rw [hc l, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem unit_entry (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (i j : Fin (2 * r + k + 1)) :
    (∑ l, star (X l i) * Hpk k r l j) + ∑ l, Hpk k r i l * X l j = 0 := by
  have h := congrFun (congrFun hU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h

theorem unit_a (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (a : Fin r) (ha : a.val + 1 < r) :
    X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) = -star (X (eI k r a) (eI k r ⟨a.val + 1, ha⟩)) := by
  have hcol : ∀ l, Hpk k r l (esI k r a) = if l = eI k r a then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r (eI k r ⟨a.val + 1, ha⟩) l = if l = esI k r ⟨a.val + 1, ha⟩ then 1 else 0 := by
    intro l
    unfold Hpk eI esI
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num | simp_all | (simp_all; omega)
  have h := unit_entry X hU (eI k r ⟨a.val + 1, ha⟩) (esI k r a)
  simp only [hcol, hrow, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  linear_combination h

theorem unit_w (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hr : 1 ≤ r) (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w w * X w (esI k r ⟨r - 1, by omega⟩) = -star (X (eI k r ⟨r - 1, by omega⟩) w) := by
  have hcol : ∀ l, Hpk k r l (esI k r ⟨r - 1, by omega⟩) = if l = eI k r ⟨r - 1, by omega⟩ then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r w l = if l = w then Hpk k r w w else 0 := fun l => hpk_W_row w l hw
  have h := unit_entry X hU w (esI k r ⟨r - 1, by omega⟩)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Finset.sum_eq_single w (fun l _ hl => by rw [hrow l, if_neg hl, zero_mul])
    (fun h' => absurd (Finset.mem_univ w) h')] at h
  linear_combination h

end dpsi

theorem dpsi_is_derivation : DpsiDerivation := by
  intro k r z' X hr hz' hU _

  let in1 : Fin (2 * r + k + 1) → ℂ := fun p => if h : p.val + 1 < r then X p ⟨p.val + 1, by omega⟩ else 0
  let in2 : Fin (2 * r + k + 1) → ℂ := fun p => if p.val + 1 = r then (X *ᵥ z') p else 0
  let in3 : Fin (2 * r + k + 1) → ℂ := fun p => -star (X (eI k r ⟨r - 1, by omega⟩) p * z' p)
  let in4 : Fin (2 * r + k + 1) → ℂ := fun p => if h : r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 then X p ⟨p.val + 1, h.2⟩ else 0
  have hrow : ∀ p : Fin (2 * r + k + 1), ∑ q, X p q * dpsiP k r z' p q =
      in1 p + in2 p + (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0)
        + in4 p := by
    intro p
    by_cases h1 : p.val + 1 < r
    · rw [Finset.sum_eq_single ⟨p.val + 1, by omega⟩]
      · rw [dp1 _ _ _ (by omega) (by simp; omega), if_pos (by simp), mul_one]
        simp only [in1, in2, in4, dif_pos h1, if_neg (show ¬ p.val + 1 = r by omega), dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        ring
      · intro q _ hq
        by_cases hq1 : q.val < r
        · rw [dp1 _ _ _ (by omega) hq1, if_neg, mul_zero]; intro h'; apply hq; ext; simp; omega
        · by_cases hq2 : q.val ≤ r + k
          · rw [dp2 _ _ _ (by omega) (by omega) hq2, if_neg (by omega), mul_zero]
          · rw [dp0 _ _ _ (by omega) (by omega), mul_zero]
      · simp
    · by_cases h2 : p.val + 1 = r
      · have hterm : ∀ q, X p q * dpsiP k r z' p q = X p q * z' q := by
          intro q
          by_cases hq1 : q.val < r
          · rw [dp1 _ _ _ (by omega) hq1, if_neg (by omega), hz' q (by omega)]
          · by_cases hq2 : q.val ≤ r + k
            · rw [dp2 _ _ _ (by omega) (by omega) hq2, if_pos h2]
            · rw [dp0 _ _ _ (by omega) (by omega), hz' q (by omega)]
        simp only [hterm, in1, in2, in4, dif_neg h1, if_pos h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        simp [Matrix.mulVec, dotProduct]
      · by_cases h3 : p.val ≤ r + k
        · rw [Finset.sum_eq_single (esI k r ⟨r - 1, by omega⟩)]
          · rw [dp3 _ _ _ (by omega) h3 (by simp [esI]; omega), if_pos (by simp [esI]; omega)]
            simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
              if_pos (show r ≤ p.val ∧ p.val ≤ r + k by omega)]
            ring
          · intro q _ hq
            by_cases hq1 : q.val ≤ r + k
            · have : ¬ (r ≤ q.val ∧ q.val ≤ r + k ∧ r + k < q.val) := by omega
              unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
            · rw [dp3 _ _ _ (by omega) h3 (by omega), if_neg, mul_zero]
              intro h'; apply hq; ext; simp [esI]; omega
          · simp
        · by_cases h4 : p.val + 1 < 2 * r + k + 1
          · rw [Finset.sum_eq_single ⟨p.val + 1, h4⟩]
            · rw [dp4 _ _ _ (by omega) (by simp; omega), if_pos (by simp), mul_one]
              simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_pos (show r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 from ⟨by omega, h4⟩),
                if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _ hq
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, if_neg, mul_zero]; intro h'; apply hq; ext; simp; omega
              · unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
            · simp
          · rw [Finset.sum_eq_zero]
            · simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
                if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, if_neg (by omega), mul_zero]
              · unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]

  have h3eq : ∀ p : Fin (2 * r + k + 1), (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0) =
      in3 p := by
    intro p
    simp only [in3]
    split_ifs with hp
    · rw [herm_Hpk_bvec_eq_star_mul_diag_of_middle z' p hp]
      have hu := unit_w X hU hr p hp
      have hsq := hpk_W_sq (k := k) p hp
      rw [star_mul']
      linear_combination (star (z' p)) * hu
        + (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp) - (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp)
    · rw [hz' p (by omega)]; simp
  simp_rw [hrow, h3eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  set L1 : ℂ := ∑ a : Fin r, if h : a.val + 1 < r then X (eI k r a) (eI k r ⟨a.val + 1, h⟩) else 0 with hL1
  set M2 : ℂ := (X *ᵥ z') (eI k r ⟨r - 1, by omega⟩) with hM2
  have s2 : ∑ p, in2 p = M2 := by
    rw [Finset.sum_eq_single (eI k r ⟨r - 1, by omega⟩)]
    · simp only [in2]; rw [if_pos (show (eI k r ⟨r - 1, by omega⟩).val + 1 = r by simp [eI]; omega)]
    · intro p _ hp; simp only [in2]; rw [if_neg]; intro h'; apply hp; ext; simp [eI]; omega
    · simp
  have s3 : ∑ p, in3 p = -star M2 := by
    simp only [in3, M2, Matrix.mulVec, dotProduct]
    rw [Finset.sum_neg_distrib, star_sum]
  have e1inj : Function.Injective (eI k r) := fun a b h => by
    have := congrArg Fin.val h; simp [eI] at this; exact Fin.ext this
  have s1 : ∑ p, in1 p = L1 := by
    rw [hL1, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨eI k r, e1inj⟩))]
    · rw [Finset.sum_map]; rfl
    · intro p _ hp
      simp only [in1]
      rw [dif_neg]
      intro h'
      apply hp
      exact Finset.mem_map.mpr ⟨⟨p.val, by omega⟩, Finset.mem_univ _, by ext; simp [eI]⟩
  have e4inj : Function.Injective (fun a : Fin r => (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h; have := congrArg Fin.val h; simp at this; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
  have s4 : ∑ p, in4 p = -star L1 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, e4inj⟩))]
    · rw [Finset.sum_map, hL1, star_sum, ← Finset.sum_neg_distrib]
      congr 1; ext a
      have hav := a.isLt
      simp only [in4, Function.Embedding.coeFn_mk]
      by_cases ha : a.val + 1 < r
      · rw [dif_pos ⟨by omega, by omega⟩, dif_pos ha]
        have hu := unit_a X hU a ha
        have e1 : (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1)) = esI k r ⟨a.val + 1, ha⟩ := by
          ext; simp [esI]; omega
        have e2 : (⟨2 * r + k - 1 - a.val + 1, by omega⟩ : Fin (2 * r + k + 1)) = esI k r a := by
          ext; simp [esI]; omega
        have hx : ∀ p q : Fin (2 * r + k + 1), p = esI k r ⟨a.val + 1, ha⟩ → q = esI k r a →
            X p q = X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) := by
          rintro p q rfl rfl; rfl
        rw [hx _ _ e1 e2, hu]
      · rw [dif_neg (by omega), dif_neg ha, star_zero, neg_zero]
    · intro p _ hp
      simp only [in4]
      rw [dif_neg]
      rintro ⟨h1, h2⟩
      apply hp
      exact Finset.mem_map.mpr ⟨⟨2 * r + k - 1 - p.val, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  rw [s1, s2, s3, s4]
  unfold dEll
  rw [← hL1, ← hM2, star_add]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
