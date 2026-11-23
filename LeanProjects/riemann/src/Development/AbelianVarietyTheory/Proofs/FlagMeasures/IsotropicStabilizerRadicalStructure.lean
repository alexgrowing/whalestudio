import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Rad

variable {k r : ℕ}

theorem cases3 {P : Fin (2 * r + k + 1) → Prop} (h1 : ∀ a, P (eI k r a)) (h2 : ∀ j, P (wI k r j))
    (h3 : ∀ b, P (esI k r b)) (i : Fin (2 * r + k + 1)) : P i := by
  by_cases h : i.val < r
  · exact h1 ⟨i.val, h⟩
  · by_cases h' : i.val ≤ r + k
    · have : i = wI k r ⟨i.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
      rw [this]; exact h2 _
    · have : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp [esI]; omega)
      rw [this]; exact h3 _

theorem eI_inj (a b : Fin r) : eI k r a = eI k r b ↔ a = b := by
  simp [eI, Fin.ext_iff]
theorem wI_inj (a b : Fin (k + 1)) : wI k r a = wI k r b ↔ a = b := by
  simp [wI, Fin.ext_iff]
theorem esI_inj (a b : Fin r) : esI k r a = esI k r b ↔ a = b := by
  have := a.2; have := b.2
  simp only [esI, Fin.ext_iff]; omega
theorem eI_ne_wI (a : Fin r) (b : Fin (k + 1)) : eI k r a ≠ wI k r b := by
  have := a.2
  simp only [eI, wI, Fin.ext_iff, ne_eq]; omega
theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  have := a.2; have := b.2
  simp only [eI, esI, Fin.ext_iff, ne_eq]; omega
theorem wI_ne_esI (a : Fin (k + 1)) (b : Fin r) : wI k r a ≠ esI k r b := by
  have := a.2; have := b.2
  simp only [wI, esI, Fin.ext_iff, ne_eq]; omega
theorem wI_ne_eI (a : Fin (k + 1)) (b : Fin r) : wI k r a ≠ eI k r b := (eI_ne_wI b a).symm
theorem esI_ne_eI (a b : Fin r) : esI k r a ≠ eI k r b := (eI_ne_esI b a).symm
theorem esI_ne_wI (a : Fin r) (b : Fin (k + 1)) : esI k r a ≠ wI k r b := (wI_ne_esI b a).symm

theorem sum3 (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = ∑ a, f (eI k r a) + ∑ j, f (wI k r j) + ∑ b, f (esI k r b) := by
  let e : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r → Fin (2 * r + k + 1) :=
    Sum.elim (Sum.elim (eI k r) (wI k r)) (esI k r)
  have he : Function.Bijective e := by
    constructor
    · rintro ((a | a) | a) ((b | b) | b) h <;>
        simp [e, eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI] at h ⊢ <;>
        exact h
    · intro i
      induction i using cases3 with
      | h1 a => exact ⟨.inl (.inl a), rfl⟩
      | h2 a => exact ⟨.inl (.inr a), rfl⟩
      | h3 a => exact ⟨.inr a, rfl⟩
  rw [← he.sum_comp f]
  simp [e, Fintype.sum_sum_type]

def sg (k : ℕ) (j : Fin (k + 1)) : ℂ := if j = Fin.last k then -1 else 1

theorem star_sg (j : Fin (k + 1)) : star (sg k j) = sg k j := by
  unfold sg; split_ifs <;> simp

theorem herm_Hb (v w : Fin (k + 1) → ℂ) : herm (Hb k) v w = ∑ j, star (w j) * (sg k j * v j) := by
  simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal, sg]

theorem herm_bvec (j : Fin (k + 1)) (w : Fin (k + 1) → ℂ) : herm (Hb k) (bvec j) w = star (w j) * sg k j := by
  rw [herm_Hb, Finset.sum_eq_single j] <;> simp +contextual [bvec]

theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then sg k i else 0 := by
  simp [Hb, Matrix.diagonal_apply, sg]

section entries
variable (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) (i j : Fin (k + 1))

theorem pEl_ee : pEl k r B S (eI k r a) (eI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold pEl
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
theorem pEl_ew : pEl k r B S (eI k r a) (wI k r j) = -(star (B a j) * sg k j) := by
  have := a.2; have := j.2
  unfold pEl; rw [if_neg (eI_ne_wI _ _), dif_pos (by simp only [eI, wI]; omega), herm_bvec]
  simp [eI, wI]
theorem pEl_es : pEl k r B S (eI k r a) (esI k r b) = S a b - herm (Hb k) (B b) (B a) / 2 := by
  have := a.2; have := b.2
  have hb : ∀ h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun h => Fin.ext (by simp only [esI]; omega)
  unfold pEl; rw [if_neg (eI_ne_esI _ _), dif_neg (by simp only [eI, esI]; omega),
    dif_neg (by simp only [eI, esI]; omega), dif_pos (by simp only [eI, esI]; omega)]
  simp only [hb]; rfl
theorem pEl_we : pEl k r B S (wI k r i) (eI k r b) = 0 := by
  have := i.2; have := b.2
  unfold pEl; rw [if_neg (wI_ne_eI _ _)]
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
theorem pEl_ww : pEl k r B S (wI k r i) (wI k r j) = if i = j then 1 else 0 := by
  have := i.2; have := j.2
  unfold pEl
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
theorem pEl_ws : pEl k r B S (wI k r i) (esI k r b) = B b i := by
  have := i.2; have := b.2
  have hb : ∀ h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun h => Fin.ext (by simp only [esI]; omega)
  unfold pEl; rw [if_neg (wI_ne_esI _ _), dif_neg (by simp only [wI, esI]; omega),
    dif_pos (by simp only [wI, esI]; omega)]
  simp only [hb]; simp [wI]
theorem pEl_se : pEl k r B S (esI k r a) (eI k r b) = 0 := by
  have := a.2; have := b.2
  unfold pEl; rw [if_neg (esI_ne_eI _ _)]
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
theorem pEl_sw : pEl k r B S (esI k r a) (wI k r j) = 0 := by
  have := a.2; have := j.2
  unfold pEl; rw [if_neg (esI_ne_wI _ _)]
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
theorem pEl_ss : pEl k r B S (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold pEl
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)

theorem H_ee : Hpk k r (eI k r a) (eI k r b) = 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI] at * <;> first | rfl | omega
theorem H_ew : Hpk k r (eI k r a) (wI k r j) = 0 := by
  have := a.2; have := j.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, wI] at * <;> first | rfl | omega
theorem H_es : Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, esI, Fin.ext_iff] at * <;> first | rfl | omega
theorem H_we : Hpk k r (wI k r i) (eI k r b) = 0 := by
  have := i.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, wI, Fin.ext_iff] at * <;> first | rfl | omega
theorem H_ww : Hpk k r (wI k r i) (wI k r j) = if i = j then sg k i else 0 := by
  have := i.2; have := j.2
  unfold Hpk sg
  split_ifs with h1 h2 h3 h4 <;> simp only [wI, Fin.ext_iff, Fin.val_last] at * <;> first | rfl | omega
theorem H_ws : Hpk k r (wI k r i) (esI k r b) = 0 := by
  have := i.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [esI, wI, Fin.ext_iff] at * <;> first | rfl | omega
theorem H_se : Hpk k r (esI k r a) (eI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, esI, Fin.ext_iff] at * <;> first | rfl | omega
theorem H_sw : Hpk k r (esI k r a) (wI k r j) = 0 := by
  have := a.2; have := j.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [esI, wI, Fin.ext_iff] at * <;> first | rfl | omega
theorem H_ss : Hpk k r (esI k r a) (esI k r b) = 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [esI, Fin.ext_iff] at * <;> first | rfl | omega

variable (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem m_ww : mEmb k r m (wI k r i) (wI k r j) = m i j := by
  have := i.2; have := j.2
  unfold mEmb; rw [dif_pos (by simp only [wI]; omega)]; simp [wI]
theorem m_e (x : Fin (2 * r + k + 1)) : mEmb k r m (eI k r a) x = if eI k r a = x then 1 else 0 := by
  have := a.2
  unfold mEmb; rw [dif_neg (by simp only [eI]; omega)]
theorem middleSpaceLeviEmbedding_apply_es_row (x : Fin (2 * r + k + 1)) : mEmb k r m (esI k r a) x = if esI k r a = x then 1 else 0 := by
  have := a.2
  unfold mEmb; rw [dif_neg (by simp only [esI]; omega)]
theorem m_we : mEmb k r m (wI k r i) (eI k r b) = 0 := by
  have := b.2
  unfold mEmb; rw [dif_neg (by simp only [eI]; omega), if_neg (wI_ne_eI _ _)]
theorem m_ws : mEmb k r m (wI k r i) (esI k r b) = 0 := by
  have := b.2
  unfold mEmb; rw [dif_neg (by simp only [esI]; omega), if_neg (wI_ne_esI _ _)]

end entries

theorem herm_star (v w : Fin (k + 1) → ℂ) : star (herm (Hb k) v w) = herm (Hb k) w v := by
  simp only [herm_Hb, star_sum, star_mul', star_star, star_sg]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem herm_add_left (v v' w : Fin (k + 1) → ℂ) :
    herm (Hb k) (v + v') w = herm (Hb k) v w + herm (Hb k) v' w := by
  simp [herm, Matrix.mulVec_add]

theorem herm_add_right (v w w' : Fin (k + 1) → ℂ) :
    herm (Hb k) v (w + w') = herm (Hb k) v w + herm (Hb k) v w' := by
  simp [herm]

theorem herm_neg_left (v w : Fin (k + 1) → ℂ) : herm (Hb k) (-v) w = -herm (Hb k) v w := by
  simp [herm, Matrix.mulVec_neg]

theorem herm_neg_right (v w : Fin (k + 1) → ℂ) : herm (Hb k) v (-w) = -herm (Hb k) v w := by
  simp [herm]

theorem pEl_mul (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ) :
    pEl k r B S * pEl k r B' S' = pEl k r (B + B')
      (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2) := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]
  · ring
  · rename_i a b
    simp only [herm_add_left, herm_add_right]
    have : herm (Hb k) (B' b) (B a) = ∑ j, (starRingEnd ℂ) (B a j) * sg k j * B' b j := by
      rw [herm_Hb]; exact Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]
    rw [← this]; ring
  · ring

theorem pEl_zero : pEl k r 0 0 = 1 := by
  ext x y
  induction x using cases3 <;> induction y using cases3 <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, Matrix.one_apply, herm,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]

theorem pEl_inv (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) :
    (pEl k r B S)⁻¹ = pEl k r (-B) (-S) := by
  apply Matrix.inv_eq_right_inv
  rw [pEl_mul, ← pEl_zero]
  congr 1
  · simp
  · ext a b; simp [herm_neg_left, herm_neg_right]

theorem pEl_mem_UH (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) :
    pEl k r B S ∈ UH (Hpk k r) := by
  show _ = _
  ext x y
  simp only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss,
      H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, apply_ite (starRingEnd ℂ)]
  · simp only [eq_comm]
  · rename_i i j
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rename_i j b
    have : (starRingEnd ℂ) (sg k j) = sg k j := star_sg j
    rw [this]; ring
  · simp only [eq_comm]
  · rename_i a b
    have h1 : herm (Hb k) (B b) (B a) = ∑ j, (starRingEnd ℂ) (B a j) * sg k j * B b j := by
      rw [herm_Hb]; exact Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]
    have h2 : (starRingEnd ℂ) (herm (Hb k) (B a) (B b)) = herm (Hb k) (B b) (B a) := herm_star _ _
    have h3 : (starRingEnd ℂ) (S b a) = -S a b := congrFun (congrFun hS a) b
    rw [← h1, h2, h3]; ring

theorem mEmb_mul (m m' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    mEmb k r m * mEmb k r m' = mEmb k r (m * m') := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, Matrix.mul_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]

theorem mEmb_one : mEmb k r 1 = 1 := by
  ext x y
  induction x using cases3 <;> induction y using cases3 <;>
    simp [m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]

theorem mEmb_mem (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k)) : mEmb k r m ∈ GG k r := by
  show _ = _
  have hm' : mᴴ * Hb k * m = Hb k := hm
  ext x y
  simp only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss,
      apply_ite (starRingEnd ℂ),
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  · simp only [eq_comm]
  · rename_i i j
    have := congrFun (congrFun hm' i) j
    simpa [Matrix.mul_apply, Hb_apply] using this
  · simp only [eq_comm]

theorem mEmb_inv (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k)) :
    (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  have hm' : mᴴ * Hb k * m = Hb k := hm
  have hH : Hb k * Hb k = 1 := by
    unfold Hb; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext j; split_ifs <;> simp
  have h1 : (Hb k * mᴴ * Hb k) * m = 1 := by
    rw [← hH]; nth_rewrite 4 [← hm']; simp only [Matrix.mul_assoc]
  have hu : IsUnit m.det := Matrix.isUnit_det_of_left_inverse h1
  apply Matrix.inv_eq_right_inv
  rw [mEmb_mul, Matrix.mul_nonsing_inv _ hu, mEmb_one]

theorem skewM_skew (s : UT r → ℂ) (t : Fin r → ℝ) : (skewM s t)ᴴ = -skewM s t := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, skewM]
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · subst h; simp
  · simp [h, h.not_gt]

theorem skewM_unique (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) :
    ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2 := by
  have hs : ∀ a b, star (S b a) = -S a b := fun a b => congrFun (congrFun hS a) b
  refine ⟨(fun q => S q.1.1 q.1.2, fun a => (S a a).im), ?_, ?_⟩
  · ext a b
    simp only [skewM]
    rcases lt_trichotomy a b with h | h | h
    · simp [h]
    · subst h
      have := congrArg Complex.re (hs a a)
      simp only [lt_irrefl, dite_false]
      apply Complex.ext <;> simp at this ⊢
      linarith
    · rw [dif_neg h.not_gt, dif_pos h, hs, neg_neg]
  · rintro ⟨s, t⟩ rfl
    ext q
    · simp [skewM, q.2]
    · simp [skewM]

theorem mulVec_bvec (g : Mat k r) (y x : Fin (2 * r + k + 1)) : (g *ᵥ bvec y) x = g x y := by
  simp [bvec]

theorem bvec_apply (y x : Fin (2 * r + k + 1)) : bvec y x = if x = y then 1 else 0 := by
  simp [bvec, Pi.single_apply]

theorem radical : ∀ k r : ℕ, (∀ (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ), (∀ a : Fin r, pEl k r B S *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ (∀ j : Fin (k + 1), pEl k r B S *ᵥ bvec (wI k r j) = bvec (wI k r j) - ∑ b, herm (Hb k) (bvec j) (B b) • bvec (eI k r b)) ∧ (∀ b : Fin r, pEl k r B S *ᵥ bvec (esI k r b) = bvec (esI k r b) + (∑ j, B b j • bvec (wI k r j)) + ∑ a, (S a b - herm (Hb k) (B b) (B a) / 2) • bvec (eI k r a)) ∧ (Sᴴ = -S → pEl k r B S ∈ Nset k r ∧ (pEl k r B S)⁻¹ = pEl k r (-B) (-S))) ∧ (∀ (s : UT r → ℂ) (t : Fin r → ℝ), (skewM s t)ᴴ = -skewM s t) ∧ (∀ S : Matrix (Fin r) (Fin r) ℂ, Sᴴ = -S → ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2) ∧ (∀ B B' (S S' : Matrix (Fin r) (Fin r) ℂ), pEl k r B S * pEl k r B' S' = pEl k r (B + B') (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2)) ∧ ∀ m ∈ UH (Hb k), mEmb k r m ∈ GG k r ∧ (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  intro k r
  refine ⟨fun B S => ⟨fun a => ?_, fun j => ?_, fun b => ?_, fun hS => ⟨⟨pEl_mem_UH B S hS, ?_, ?_⟩, pEl_inv B S⟩⟩,
    skewM_skew, skewM_unique, pEl_mul, fun m hm => ⟨mEmb_mem m hm, mEmb_inv m hm⟩⟩
  · funext x
    rw [mulVec_bvec, bvec_apply]
    induction x using cases3 <;> simp [pEl_ee, pEl_we, pEl_se, eI_inj, wI_ne_eI, esI_ne_eI]
  · funext x
    rw [mulVec_bvec]
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, bvec_apply, herm_bvec]
    induction x using cases3 <;>
      simp [pEl_ew, pEl_ww, pEl_sw, eI_inj, wI_inj, wI_ne_eI, esI_ne_eI, eI_ne_wI, esI_ne_wI]
  · funext x
    rw [mulVec_bvec]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, bvec_apply]
    induction x using cases3 <;>
      simp [pEl_es, pEl_ws, pEl_ss, eI_inj, wI_inj, esI_inj, wI_ne_eI, esI_ne_eI, eI_ne_wI, esI_ne_wI,
        eI_ne_esI, wI_ne_esI]
  · intro a x _
    induction x using cases3 <;> simp [pEl_ee, pEl_we, pEl_se, eI_inj, wI_ne_eI, esI_ne_eI]
  · intro x y h1 h2 h3
    induction x using cases3 with
    | h1 a => exact absurd a.2 (by simp only [eI] at h3; omega)
    | h2 i =>
      induction y using cases3 with
      | h1 a => exact absurd a.2 (by simp only [eI] at h1; omega)
      | h2 j => simp [pEl_ww, wI_inj]
      | h3 a => exact absurd a.2 (by simp only [esI] at h2; omega)
    | h3 b =>
      induction y using cases3 with
      | h1 a => exact absurd a.2 (by simp only [eI] at h1; omega)
      | h2 j => simp [pEl_sw, esI_ne_wI]
      | h3 a => exact absurd a.2 (by simp only [esI] at h2; omega)

end GlobalTheory.Amp.Rad
