import Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantReindex

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x2 CardInsertEmbedding DeterminantReindex

lemma det_submatrix_unitriangular_eq_one {m k : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : u ∈ C2.UTset m) (e : Fin k → Fin m)
    (he : ∀ t, (e t).val = t.val) : (u.submatrix e e).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply, hu.2, Finset.prod_const_one]
  · intro t s h
    simp only [Matrix.submatrix_apply]
    apply hu.1
    rw [Fin.lt_def, he, he]
    exact h

lemma lower_parabolic_entry_zero {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LPg (C2.monoP w d)) (x y : Fin m) (hxy : x < y) :
    l (w x) (w y) = 0 := by
  have := hl.2.1 x y hxy
  rw [monomialMatrix_conj_apply w d hd] at this
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (inv_ne_zero (hd x))
    · exact h'
  · exact absurd h (hd y)

theorem lower_minor_identity : C2.MinorL := by
  intro m w d hd a i hi
  have ham : a.val + 1 ≤ m := a.isLt
  have hR0c : (C2.wSet w (a.val + 1)).card = a.val + 1 := c2x3_wSet_card w ham
  have hIc : (C2.iSet m (a.val + 1)).card = a.val + 1 := c2x3_iSet_card ham
  have hR'c : (insert i (C2.wSet w a.val)).card = a.val + 1 := by
    rw [Finset.card_insert_of_notMem hi, c2x3_wSet_card w (by omega)]
  set eR0 := (C2.wSet w (a.val + 1)).orderEmbOfFin rfl with heR0
  set eR' := (insert i (C2.wSet w a.val)).orderEmbOfFin rfl with heR'
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : Fin (C2.wSet w (a.val + 1)).card → Fin m,
      ∀ t, ρ0 t = w ⟨t.val, by have := t.isLt; omega⟩ := ⟨fun t => w ⟨t.val, by have := t.isLt; omega⟩, fun t => rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin (insert i (C2.wSet w a.val)).card → Fin m,
      ∀ t, ρ t = if ht : t.val < a.val then w ⟨t.val, by omega⟩ else i :=
    ⟨fun t => if ht : t.val < a.val then w ⟨t.val, by omega⟩ else i, fun t => rfl⟩
  obtain ⟨τ0, hτ0⟩ := perm_of_range eR0 ρ0 eR0.injective (fun t => by
    have := Finset.orderEmbOfFin_mem (C2.wSet w (a.val + 1)) rfl t
    obtain ⟨j, hj, hw⟩ := Finset.mem_image.mp this
    have hjv : j.val < a.val + 1 := by simpa [C2.iSet] using hj
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    rw [hρ0, ← hw])
  obtain ⟨τ, hτ⟩ := perm_of_range eR' ρ eR'.injective (fun t => by
    have := Finset.orderEmbOfFin_mem (insert i (C2.wSet w a.val)) rfl t
    rcases Finset.mem_insert.mp this with h | h
    · refine ⟨⟨a.val, by omega⟩, ?_⟩
      rw [hρ, dif_neg (lt_irrefl _)]; exact h.symm
    · obtain ⟨j, hj, hw⟩ := Finset.mem_image.mp h
      have hjv : j.val < a.val := by simpa [C2.iSet] using hj
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      rw [hρ, dif_pos hjv, ← hw])
  refine ⟨((Equiv.Perm.sign τ0 : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ), ?_, fun l hl u' hu => ?_⟩
  · rcases sign_pm τ0 with h0 | h0 <;> rcases sign_pm τ with h1 | h1 <;> rw [h0, h1] <;> norm_num
  unfold C2.minorS
  rw [dif_pos (hR0c.trans hIc.symm), dif_pos (hR'c.trans hIc.symm)]
  set eI := (C2.iSet m (a.val + 1)).orderEmbOfFin (hR0c.trans hIc.symm).symm with heI
  set eI' := (C2.iSet m (a.val + 1)).orderEmbOfFin (hR'c.trans hIc.symm).symm with heI'
  have hI : ∀ t, (eI t).val = t.val := fun t => iemb ham _ t
  have hI' : ∀ t, (eI' t).val = t.val := fun t => iemb ham _ t
  rw [U_mul_sub (by omega) (l * C2.monoP w d) u' (fun x y h => hu.1 x y h) eR' eI' hI', Matrix.det_mul,
    det_submatrix_unitriangular_eq_one u' hu eI' hI', mul_one, submatrix_mul_monomialMatrix, Matrix.det_mul, Matrix.det_diagonal,
    det_reindex l eR' ρ _ τ hτ]
  conv_lhs => rw [← Matrix.one_mul (C2.monoP w d)]
  rw [submatrix_mul_monomialMatrix, Matrix.det_mul, Matrix.det_diagonal, det_reindex 1 eR0 ρ0 _ τ0 hτ0]
  have h1 : ((1 : Matrix (Fin m) (Fin m) ℂ).submatrix ρ0 (fun s => w (eI s))).det = 1 := by
    have : (1 : Matrix (Fin m) (Fin m) ℂ).submatrix ρ0 (fun s => w (eI s)) = 1 := by
      ext t s
      simp only [Matrix.submatrix_apply, Matrix.one_apply, hρ0]
      by_cases hts : t = s
      · subst hts; rw [if_pos (congrArg w (Fin.ext (hI t).symm)), if_pos rfl]
      · rw [if_neg, if_neg hts]
        intro e; apply hts
        have := congrArg Fin.val (w.injective e); simp only [hI] at this; exact Fin.ext this
    rw [this, Matrix.det_one]
  have hL : (l.submatrix ρ (fun s => w (eI' s))).det = l i (w a) := by
    rw [Matrix.det_of_lowerTriangular]
    · have ht0 : a.val < (insert i (C2.wSet w a.val)).card := by omega
      rw [Finset.prod_eq_single ⟨a.val, ht0⟩]
      · simp only [Matrix.submatrix_apply, hρ, dif_neg (lt_irrefl _)]
        congr 2; exact Fin.ext (hI' _)
      · intro t _ ht
        have htv : t.val < a.val := by
          have := t.isLt; have : t.val ≠ a.val := fun e => ht (Fin.ext e); omega
        simp only [Matrix.submatrix_apply, hρ, dif_pos htv]
        have : eI' t = ⟨t.val, by omega⟩ := Fin.ext (hI' t)
        rw [this]; exact hl.1.2 _
      · simp
    · intro t s hts
      have hts' : t.val < s.val := by
        have := OrderDual.toDual_lt_toDual.mp hts; rw [Fin.lt_def] at this; exact this
      have htv : t.val < a.val := by have := s.isLt; omega
      simp only [Matrix.submatrix_apply, hρ, dif_pos htv]
      have : eI' s = ⟨s.val, by have := s.isLt; omega⟩ := Fin.ext (hI' s)
      rw [this]
      exact lower_parabolic_entry_zero w d hd l hl _ _ (by rw [Fin.lt_def]; exact hts')
  rw [h1, hL, prod_emb hR0c d eI hI, prod_emb hR'c d eI' hI']
  linear_combination (-(((Equiv.Perm.sign τ0 : ℤ) : ℂ) * l i (w a) *
    ∏ j ∈ Finset.range (a.val + 1), (if h : j < m then d ⟨j, h⟩ else 1))) * sign_sq τ

end Formalism.FourierDecayAlt.P
