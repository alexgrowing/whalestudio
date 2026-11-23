import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.InvEig

open Matrix

noncomputable section

theorem neg_one_sq (p : ℕ) : ((-1 : ℂ) ^ p) * (-1) ^ p - 1 = 0 := by
  rw [← mul_pow]; simp

theorem core_col {N : ℕ} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (η : Fin (N + 1) → ℂ) (h : T *ᵥ η = η)
    (j : Fin (N + 1)) :
    ∑ p, η p * ((-1 : ℂ) ^ (p : ℕ) * (T.submatrix p.succAbove j.succAbove).det) =
      (-1 : ℂ) ^ (j : ℕ) * (T.det * η j) := by
  have kj : ∑ p, T.adjugate j p * η p = T.det * η j := by
    have := congrFun (congrArg (fun M => M *ᵥ η) (adjugate_mul T)) j
    rw [← mulVec_mulVec, h] at this
    simpa [mulVec, dotProduct, Matrix.one_apply] using this
  rw [← kj, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have E := adjugate_fin_succ_eq_det_submatrix T j p
  linear_combination (-(-1 : ℂ) ^ (j : ℕ) * η p) * E -
    (η p * (-1 : ℂ) ^ (p : ℕ) * (T.submatrix p.succAbove j.succAbove).det) * (neg_one_sq (j : ℕ))

theorem core_row {N : ℕ} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (η : Fin (N + 1) → ℂ) (h : η ᵥ* T = η)
    (j : Fin (N + 1)) :
    ∑ p, η p * ((-1 : ℂ) ^ (p : ℕ) * (T.submatrix j.succAbove p.succAbove).det) =
      (-1 : ℂ) ^ (j : ℕ) * (T.det * η j) := by
  have h' : Tᵀ *ᵥ η = η := by rw [mulVec_transpose]; exact h
  have := core_col Tᵀ η h' j
  rw [det_transpose] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← transpose_submatrix, det_transpose]

theorem smono_succAbove {N : ℕ} (f : Fin N → Fin (N + 1)) (hf : StrictMono f) :
    ∃ j : Fin (N + 1), f = j.succAbove := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, ∀ l, f l ≠ j := by
    by_contra hc
    push Not at hc
    have hs : Function.Surjective f := fun j => by obtain ⟨l, hl⟩ := hc j; exact ⟨l, hl⟩
    have := Fintype.card_le_of_surjective f hs
    simp at this
  have hcard : (Finset.univ.erase j).card = N := by simp [Finset.card_erase_of_mem]
  have h1 := Finset.orderEmbOfFin_unique hcard (f := f) (fun x => by simp [hj x]) hf
  have h2 := Finset.orderEmbOfFin_unique hcard (f := j.succAbove) (fun x => by simp [Fin.succAbove_ne])
    (Fin.strictMono_succAbove j)
  exact ⟨j, h1.trans h2.symm⟩

variable {k r : ℕ}

def eV (k r : ℕ) (p : Fin (r + k + 1)) : Fin (2 * r + k + 1) := ⟨r + p.val, by have := p.isLt; omega⟩

def e0 (k r : ℕ) (p : Fin (r + k + 1)) : Fin (2 * r + k + 1) := ⟨p.val, by have := p.isLt; omega⟩

theorem colsV_eq (t : Fin (k + 1)) :
    colsV k r t = eV k r ∘ (⟨t.val, by have := t.isLt; omega⟩ : Fin (r + k + 1)).succAbove := by
  funext l
  apply Fin.ext
  simp only [colsV, eV, Function.comp_apply, Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega

theorem rowsR_eq (i : Fin (k + 1)) :
    rowsR k r i = e0 k r ∘ (⟨r + i.val, by have := i.isLt; omega⟩ : Fin (r + k + 1)).succAbove := by
  funext l
  apply Fin.ext
  simp only [rowsR, e0, Function.comp_apply, Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega

theorem w_col_e {z' : Fin (2 * r + k + 1) → ℂ} {w : B.Mat k r} (hw : w ∈ UWset k r z') (q : Fin (2 * r + k + 1))
    (hq : q.val < r) (y : Fin (2 * r + k + 1)) : w y q = if y = q then 1 else 0 := by
  have h1 := congrFun (hw.2.1 ⟨q.val, hq⟩).1 y
  have e : eI k r ⟨q.val, hq⟩ = q := Fin.ext rfl
  rw [e] at h1
  simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using h1

theorem m_col_e {m : B.Mat k r} (hm : m ∈ Nset k r) (q i : Fin (2 * r + k + 1)) (hq : q.val < r) (hi : q.val ≤ i.val) :
    m i q = if i = q then 1 else 0 := by
  have := hm.2.1 ⟨q.val, hq⟩ i hi
  have e : eI k r ⟨q.val, hq⟩ = q := Fin.ext rfl
  rwa [e] at this

theorem mw_X {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r} (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r)
    (i q : Fin (2 * r + k + 1)) (hi : r ≤ i.val) (hq : q.val < r) : (m * w) i q = 0 := by
  rw [Matrix.mul_apply]
  simp only [w_col_e hw q hq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [m_col_e hm q i hq (by omega), if_neg]
  intro h; subst h; omega

end

end Formalism.FourierDecayAlt.P.CutMP.InvEig

namespace Formalism.FourierDecayAlt.P.CutMP.InvEig

open Matrix

noncomputable section

variable {k r : ℕ}

theorem sum_emb {a b : ℕ} (f : Fin a → Fin b) (hf : Function.Injective f) (G : Fin b → ℂ)
    (hG : ∀ q, (∀ p, f p ≠ q) → G q = 0) : ∑ p, G (f p) = ∑ q, G q := by
  classical
  calc ∑ p, G (f p) = ∑ q ∈ Finset.univ.map ⟨f, hf⟩, G q := by rw [Finset.sum_map]; rfl
    _ = ∑ q, G q := Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => hG q (fun p hp => hq (by
        simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨p, hp⟩)))

theorem eV_inj : Function.Injective (eV k r) := fun a b h => by
  simp only [eV, Fin.ext_iff] at h; exact Fin.ext (by omega)

theorem index_embedding_injective : Function.Injective (e0 k r) := fun a b h => by
  simp only [e0, Fin.ext_iff] at h; exact Fin.ext h

theorem comp_inj {a b c : ℕ} {e : Fin b → Fin c} (he : Function.Injective e) {f g : Fin a → Fin b}
    (h : e ∘ f = e ∘ g) : f = g := funext fun l => he (congrFun h l)

theorem nilpotent_column_anisotropic {m : B.Mat k r} (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) (hi : r ≤ i.val) : m i j = if i = j then 1 else 0 :=
  hm.2.2 i j hj1 hj2 hi

theorem mw_colX {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r} (hw : w ∈ UWset k r z')
    (i q : Fin (2 * r + k + 1)) (hq : q.val < r) : (m * w) i q = m i q := by
  rw [Matrix.mul_apply]
  simp only [w_col_e hw q hq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem nilpotent_unitary_fixes_tail {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r} (hz' : inWb k r z') (hw : w ∈ UWset k r z')
    (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : ((m * w) *ᵥ z') i = z' i := by
  rw [← Matrix.mulVec_mulVec, hw.2.2]
  have e : ∀ j, m i j * z' j = (if i = j then 1 else 0) * z' j := by
    intro j
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [nilpotent_column_anisotropic hm i j hj.1 hj.2 hi]
    · rw [hz' j (by omega), mul_zero, mul_zero]
  simp only [Matrix.mulVec, dotProduct, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

def TV (k r : ℕ) (S : B.Mat k r) : Matrix (Fin (r + k + 1)) (Fin (r + k + 1)) ℂ := S.submatrix (eV k r) (eV k r)

theorem TV_fix {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r} (hz' : inWb k r z') (hw : w ∈ UWset k r z')
    (hm : m ∈ Nset k r) : TV k r (m * w) *ᵥ (fun p => z' (eV k r p)) = fun p => z' (eV k r p) := by
  funext i
  have h := nilpotent_unitary_fixes_tail hz' hw hm (eV k r i) (by simp [eV])
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, TV, Matrix.submatrix_apply]
  refine sum_emb (eV k r) eV_inj (fun q => (m * w) (eV k r i) q * z' q) (fun q hq => ?_)
  have : q.val < r := by
    by_contra hc
    exact hq ⟨q.val - r, by have := q.isLt; omega⟩ (Fin.ext (by simp [eV]; omega))
  rw [hz' q (Or.inl this), mul_zero]

def eVEquiv (k r : ℕ) : Fin (r + k + 1) ≃ {a : Fin (2 * r + k + 1) // ¬ a.val < r} where
  toFun p := ⟨eV k r p, by simp [eV]⟩
  invFun a := ⟨a.1.val - r, by have := a.1.isLt; have := a.2; omega⟩
  left_inv p := by ext; simp [eV]
  right_inv a := by ext; simp [eV]; have := a.2; omega

theorem det_mw_V {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r} (hw : w ∈ UWset k r z')
    (hm : m ∈ Nset k r) : (m * w).det = (TV k r (m * w)).det := by
  classical
  rw [Matrix.twoBlockTriangular_det (m * w) (fun i => i.val < r) (fun i hi j hj => mw_X hw hm i j (by omega) hj)]
  have h1 : ((m * w).toSquareBlockProp (fun i => i.val < r)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_eq_one (fun i _ => ?_)
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock_apply]
      rw [mw_colX hw _ _ i.2, m_col_e hm i.1 i.1 i.2 le_rfl, if_pos rfl]
    · intro i j hij
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock_apply]
      rw [mw_colX hw _ _ j.2, m_col_e hm j.1 i.1 j.2 (le_of_lt hij), if_neg]
      intro h; exact (ne_of_lt hij) (Subtype.ext h).symm
  have h2 : ((m * w).toSquareBlockProp (fun i => ¬ i.val < r)).det = (TV k r (m * w)).det := by
    rw [← Matrix.det_submatrix_equiv_self (eVEquiv k r)]
    rfl
  rw [h1, h2, one_mul]

theorem betaM_d {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r} (hz' : inWb k r z') (hw : w ∈ UWset k r z')
    (hm : m ∈ Nset k r) (d : Fin (r + k) → Fin (2 * r + k + 1)) (hd : StrictMono d) :
    ∑ t, beM k r z' t * ((m * w).submatrix (colsV k r t) d).det =
      (m * w).det * ∑ t, beM k r z' t * (if d = colsV k r t then 1 else 0) := by
  classical
  by_cases hX : ∃ l, (d l).val < r
  · obtain ⟨l, hl⟩ := hX
    have h0 : ∀ t, ((m * w).submatrix (colsV k r t) d).det = 0 := fun t =>
      Matrix.det_eq_zero_of_column_eq_zero l (fun i => by
        simp only [Matrix.submatrix_apply]
        exact mw_X hw hm _ _ (by simp only [colsV]; split_ifs <;> omega) hl)
    have h1 : ∀ t, d ≠ colsV k r t := fun t h => by
      have := congrFun h l
      rw [this] at hl
      simp only [colsV] at hl
      split_ifs at hl <;> omega
    simp [h0, h1]
  · push Not at hX
    set d' : Fin (r + k) → Fin (r + k + 1) := fun l => ⟨(d l).val - r, by have := (d l).isLt; omega⟩ with hd'def
    have hd' : StrictMono d' := fun a b hab => by
      have := hd hab
      have := hX a
      have := hX b
      simp only [d', Fin.lt_def] at *
      omega
    obtain ⟨j, hj⟩ := smono_succAbove d' hd'
    have hdj : d = eV k r ∘ j.succAbove := by
      funext l
      apply Fin.ext
      have h1 := congrFun hj l
      have h2 := hX l
      simp only [d', Fin.ext_iff] at h1
      simp only [eV, Function.comp_apply]
      omega
    set T := TV k r (m * w) with hTdef
    set η : Fin (r + k + 1) → ℂ := fun p => z' (eV k r p) with hηdef
    have hT : T *ᵥ η = η := TV_fix hz' hw hm
    have hη : ∀ p : Fin (r + k + 1), k < p.val → η p = 0 := fun p hp =>
      hz' _ (Or.inr (by simp [eV]; omega))
    have hwI : ∀ t : Fin (k + 1), wI k r t = eV k r ⟨t.val, by have := t.isLt; omega⟩ := fun t => Fin.ext rfl
    have emb_inj : Function.Injective (fun t : Fin (k + 1) => (⟨t.val, by have := t.isLt; omega⟩ : Fin (r + k + 1))) :=
      fun a b h => Fin.ext (by simpa using h)
    have notin : ∀ q : Fin (r + k + 1), (∀ t : Fin (k + 1), (⟨t.val, by have := t.isLt; omega⟩ : Fin (r + k + 1)) ≠ q) →
        k < q.val := fun q hq => by
      by_contra hc
      exact hq ⟨q.val, by omega⟩ (Fin.ext rfl)
    have lhs : ∑ t, beM k r z' t * ((m * w).submatrix (colsV k r t) d).det =
        ∑ p, η p * ((-1 : ℂ) ^ (p : ℕ) * (T.submatrix p.succAbove j.succAbove).det) := by
      rw [← sum_emb _ emb_inj (fun p => η p * ((-1 : ℂ) ^ (p : ℕ) * (T.submatrix p.succAbove j.succAbove).det))
        (fun q hq => by rw [hη q (notin q hq), zero_mul])]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [colsV_eq, hdj, beM, hwI]
      simp only [hTdef, TV, Matrix.submatrix_submatrix, hηdef]
      ring
    have rhs : ∑ t, beM k r z' t * (if d = colsV k r t then 1 else 0) = (-1 : ℂ) ^ (j : ℕ) * η j := by
      have e1 : ∀ t : Fin (k + 1), beM k r z' t * (if d = colsV k r t then 1 else 0) =
          (fun p : Fin (r + k + 1) => if j = p then η p * (-1 : ℂ) ^ (p : ℕ) else 0)
            ⟨t.val, by have := t.isLt; omega⟩ := by
        intro t
        dsimp only
        have iff : d = colsV k r t ↔ j = ⟨t.val, by have := t.isLt; omega⟩ := by
          rw [colsV_eq, hdj]
          constructor
          · intro h; exact Fin.succAbove_left_injective (comp_inj eV_inj h)
          · intro h; rw [h]
        by_cases h : j = ⟨t.val, by have := t.isLt; omega⟩
        · rw [if_pos (iff.2 h), if_pos h, beM, hwI]
          simp only [hηdef]
          ring
        · rw [if_neg (fun h' => h (iff.1 h')), if_neg h, mul_zero]
      simp only [e1]
      rw [sum_emb _ emb_inj (fun p : Fin (r + k + 1) => if j = p then η p * (-1 : ℂ) ^ (p : ℕ) else 0)
        (fun q hq => by split_ifs <;> simp [hη q (notin q hq)])]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      ring
    rw [lhs, core_col T η hT j, rhs, det_mw_V hw hm]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.InvEig

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix InvEig

theorem colsV_smono {k r : ℕ} (t : Fin (k + 1)) : StrictMono (colsV k r t) := by
  rw [colsV_eq]
  intro a b h
  have := Fin.strictMono_succAbove (⟨t.val, by have := t.isLt; omega⟩ : Fin (r + k + 1)) h
  simp only [Function.comp_apply, eV, Fin.lt_def] at this ⊢
  omega

theorem inverse_beta_minus_holds : RInvBetaM := by
  intro k r z' w m hz' hw hm M _ _ X
  classical
  have hmem : ∀ t, colsV k r t ∈ jSetR k r := fun t => by
    simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]; exact colsV_smono t
  have e1 : ∀ d ∈ jSetR k r, (∑ t, beM k r z' t * ((m * w).submatrix (colsV k r t) d).det) • X d =
      ∑ t, ((m * w).det * beM k r z' t) • (if d = colsV k r t then X d else 0) := by
    intro d hd
    have hd' : StrictMono d := by simpa [jSetR] using hd
    rw [betaM_d hz' hw hm d hd', Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    split_ifs <;> simp [mul_assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Finset.smul_sum, Finset.sum_ite_eq', if_pos (hmem t), smul_smul]

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutMP.InvEig

open Matrix

noncomputable section

variable {k r : ℕ}

theorem zeta_zero {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (q : Fin (2 * r + k + 1)) (hq : q.val < r) :
    herm (Hpk k r) (bvec q) z' = 0 := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.star_apply]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  by_cases hx : r ≤ x.val ∧ x.val ≤ r + k
  · have : Hpk k r x q = 0 := by
      unfold Hpk
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    rw [this, mul_zero]
  · rw [hz' x (by omega)]; simp

theorem rowsR_smono (i : Fin (k + 1)) : StrictMono (rowsR k r i) := by
  rw [rowsR_eq]
  intro a b h
  have := Fin.strictMono_succAbove (⟨r + i.val, by have := i.isLt; omega⟩ : Fin (r + k + 1)) h
  simp only [Function.comp_apply, e0, Fin.lt_def] at this ⊢
  omega

theorem conclusion₃ {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (P : B.Mat k r)
    (hPV0 : ∀ i j : Fin (2 * r + k + 1), r + k < i.val → j.val ≤ r + k → P i j = 0)
    (hdet : P.det = (P.submatrix (e0 k r) (e0 k r)).det)
    (hζ : (fun p => herm (Hpk k r) (bvec (e0 k r p)) z') ᵥ* (P.submatrix (e0 k r) (e0 k r)) =
      (fun p => herm (Hpk k r) (bvec (e0 k r p)) z'))
    (c : Fin (r + k) → Fin (2 * r + k + 1)) (hc : StrictMono c) :
    ∑ i, alP k r z' i * (P.submatrix c (rowsR k r i)).det =
      P.det * ∑ i, alP k r z' i * (if c = rowsR k r i then 1 else 0) := by
  classical
  have hR : ∀ (i : Fin (k + 1)) (l : Fin (r + k)), (rowsR k r i l).val ≤ r + k := fun i l => by
    simp only [rowsR]; split_ifs <;> omega
  by_cases hX : ∃ l, r + k < (c l).val
  · obtain ⟨l, hl⟩ := hX
    have h0 : ∀ i, (P.submatrix c (rowsR k r i)).det = 0 := fun i =>
      Matrix.det_eq_zero_of_row_eq_zero l (fun j => by
        simp only [Matrix.submatrix_apply]
        exact hPV0 _ _ hl (hR i j))
    have h1 : ∀ i, c ≠ rowsR k r i := fun i h => by
      have := congrFun h l
      rw [this] at hl
      have := hR i l
      omega
    simp [h0, h1]
  · push Not at hX
    set c' : Fin (r + k) → Fin (r + k + 1) := fun l => ⟨(c l).val, by have := hX l; omega⟩ with hc'def
    have hc' : StrictMono c' := fun a b hab => by
      have := hc hab
      simp only [c', Fin.lt_def] at *
      omega
    obtain ⟨j, hj⟩ := smono_succAbove c' hc'
    have hcj : c = e0 k r ∘ j.succAbove := by
      funext l
      apply Fin.ext
      have h1 := congrFun hj l
      simp only [c', Fin.ext_iff] at h1
      simp only [e0, Function.comp_apply]
      omega
    set T := P.submatrix (e0 k r) (e0 k r) with hTdef
    set ζ : Fin (r + k + 1) → ℂ := fun p => herm (Hpk k r) (bvec (e0 k r p)) z' with hζdef
    have hζ0 : ∀ p : Fin (r + k + 1), p.val < r → ζ p = 0 := fun p hp => zeta_zero hz' _ (by simp [e0]; omega)
    have hwI : ∀ i : Fin (k + 1), wI k r i = e0 k r ⟨r + i.val, by have := i.isLt; omega⟩ := fun i => Fin.ext rfl
    have emb_inj : Function.Injective
        (fun i : Fin (k + 1) => (⟨r + i.val, by have := i.isLt; omega⟩ : Fin (r + k + 1))) :=
      fun a b h => Fin.ext (by simp only [Fin.mk.injEq] at h; omega)
    have notin : ∀ q : Fin (r + k + 1),
        (∀ i : Fin (k + 1), (⟨r + i.val, by have := i.isLt; omega⟩ : Fin (r + k + 1)) ≠ q) → q.val < r :=
      fun q hq => by
        by_contra hc
        exact hq ⟨q.val - r, by have := q.isLt; omega⟩ (Fin.ext (by simp only; omega))
    have hs : ∀ i : ℕ, (-1 : ℂ) ^ i = (-1 : ℂ) ^ r * (-1 : ℂ) ^ (r + i) := fun i => by
      rw [pow_add, ← mul_assoc, ← mul_pow]; simp
    have lhs : ∑ i, alP k r z' i * (P.submatrix c (rowsR k r i)).det =
        (-1 : ℂ) ^ r * ∑ p, ζ p * ((-1 : ℂ) ^ (p : ℕ) * (T.submatrix j.succAbove p.succAbove).det) := by
      rw [Finset.mul_sum, ← sum_emb _ emb_inj
        (fun p => (-1 : ℂ) ^ r * (ζ p * ((-1 : ℂ) ^ (p : ℕ) * (T.submatrix j.succAbove p.succAbove).det)))
        (fun q hq => by rw [hζ0 q (notin q hq)]; ring)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [rowsR_eq, hcj, alP, hwI, hs (i : ℕ)]
      simp only [hTdef, Matrix.submatrix_submatrix, hζdef]
      ring
    have rhs : ∑ i, alP k r z' i * (if c = rowsR k r i then 1 else 0) =
        (-1 : ℂ) ^ r * ((-1 : ℂ) ^ (j : ℕ) * ζ j) := by
      have e1 : ∀ i : Fin (k + 1), alP k r z' i * (if c = rowsR k r i then 1 else 0) =
          (fun p : Fin (r + k + 1) => if j = p then (-1 : ℂ) ^ r * ((-1 : ℂ) ^ (p : ℕ) * ζ p) else 0)
            ⟨r + i.val, by have := i.isLt; omega⟩ := by
        intro i
        dsimp only
        have iff : c = rowsR k r i ↔ j = ⟨r + i.val, by have := i.isLt; omega⟩ := by
          rw [rowsR_eq, hcj]
          constructor
          · intro h; exact Fin.succAbove_left_injective (comp_inj index_embedding_injective h)
          · intro h; rw [h]
        by_cases h : j = ⟨r + i.val, by have := i.isLt; omega⟩
        · rw [if_pos (iff.2 h), if_pos h, alP, hwI, hs (i : ℕ)]
          simp only [hζdef]
          ring
        · rw [if_neg (fun h' => h (iff.1 h')), if_neg h, mul_zero]
      simp only [e1]
      rw [sum_emb _ emb_inj (fun p : Fin (r + k + 1) => if j = p then (-1 : ℂ) ^ r * ((-1 : ℂ) ^ (p : ℕ) * ζ p) else 0)
        (fun q hq => by split_ifs <;> simp [hζ0 q (notin q hq)])]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
    rw [lhs, core_row T ζ hζ j, rhs, hdet]
    ring

theorem usage₅ {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (P : B.Mat k r)
    (hPV0 : ∀ i j : Fin (2 * r + k + 1), r + k < i.val → j.val ≤ r + k → P i j = 0)
    (hdet : P.det = (P.submatrix (e0 k r) (e0 k r)).det)
    (hζ : (fun p => herm (Hpk k r) (bvec (e0 k r p)) z') ᵥ* (P.submatrix (e0 k r) (e0 k r)) =
      (fun p => herm (Hpk k r) (bvec (e0 k r p)) z'))
    (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M) :
    ∑ c ∈ jSetR k r, (∑ i : Fin (k + 1), alP k r z' i * (P.submatrix c (rowsR k r i)).det) • X c =
      P.det • ∑ i : Fin (k + 1), alP k r z' i • X (rowsR k r i) := by
  classical
  have hmem : ∀ i, rowsR k r i ∈ jSetR k r := fun i => by
    simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]; exact rowsR_smono i
  have e1 : ∀ c ∈ jSetR k r, (∑ i, alP k r z' i * (P.submatrix c (rowsR k r i)).det) • X c =
      ∑ i, (P.det * alP k r z' i) • (if c = rowsR k r i then X c else 0) := by
    intro c hc
    have hc' : StrictMono c := by simpa [jSetR] using hc
    rw [conclusion₃ hz' P hPV0 hdet hζ c hc', Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp [mul_assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.smul_sum, Finset.sum_ite_eq', if_pos (hmem i), smul_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.InvEig
