import Formalism.FormalDegreeBessel.StatementG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.QuantumDeterminants

def ggLastU (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i = Fin.last n ∧ j = Fin.last n then 1 else 0

lemma ggDet_swapBlocks (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) =
      fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) * fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (-(1 : Matrix (Fin m) (Fin m) ℂ)) (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) * fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (-(1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [det_mul, det_neg]

lemma ggDet_updateCol_last_single (n : ℕ) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_column _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have : (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove = Z.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last, updateCol_apply, (Fin.castSucc_lt_last j).ne]
    rw [this]
    simp only [updateCol_self, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
  · intro i _ hi
    simp [updateCol_apply, Pi.single_apply, hi]
  · simp

lemma ggDet_keyN (n : ℕ) (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (α β : ℂ) :
    (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W).det =
      Z.det * W.det - α * β * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det := by
  have h1 : fromBlocks Z (α • ggLastU n) (β • ggLastU n) W =
      updateCol (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W) (Sum.inr (Fin.last n))
        ((Sum.elim (0 : Fin (n + 1) → ℂ) (fun a => W a (Fin.last n))) + α • (Sum.elim (Pi.single (Fin.last n) (1 : ℂ)) (0 : Fin (n + 1) → ℂ))) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e1 : updateCol (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W) (Sum.inr (Fin.last n))
      (Sum.elim (0 : Fin (n + 1) → ℂ) (fun a => W a (Fin.last n))) = fromBlocks Z 0 (β • ggLastU n) W := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e2 : updateCol (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W) (Sum.inr (Fin.last n))
      (Sum.elim (Pi.single (Fin.last n) (1 : ℂ)) (0 : Fin (n + 1) → ℂ)) =
        fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have h2 : fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0) =
      updateCol (fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0))
        (Sum.inl (Fin.last n))
        ((Sum.elim (fun a => Z a (Fin.last n)) (0 : Fin (n + 1) → ℂ)) + β • (Sum.elim (0 : Fin (n + 1) → ℂ) (Pi.single (Fin.last n) (1 : ℂ)))) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e3 : updateCol (fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0))
        (Sum.inl (Fin.last n)) (Sum.elim (fun a => Z a (Fin.last n)) (0 : Fin (n + 1) → ℂ)) =
      fromBlocks Z (ggLastU n) 0 (updateCol W (Fin.last n) 0) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e4 : updateCol (fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0))
        (Sum.inl (Fin.last n)) (Sum.elim (0 : Fin (n + 1) → ℂ) (Pi.single (Fin.last n) (1 : ℂ))) =
      fromBlocks (updateCol Z (Fin.last n) 0) (ggLastU n) (ggLastU n) (updateCol W (Fin.last n) 0) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e5 : (fromBlocks (updateCol Z (Fin.last n) 0) (ggLastU n) (ggLastU n)
        (updateCol W (Fin.last n) 0)).submatrix id
        (Equiv.swap (Sum.inl (Fin.last n)) (Sum.inr (Fin.last n))) =
      fromBlocks (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)) 0 0
        (updateCol W (Fin.last n) (Pi.single (Fin.last n) 1)) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj, Equiv.swap_apply_def]
  have hW0 : (updateCol W (Fin.last n) 0).det = 0 :=
    det_eq_zero_of_column_eq_zero (Fin.last n) (fun i => by simp)
  have hP := det_permute' (Equiv.swap (Sum.inl (Fin.last n)) (Sum.inr (Fin.last n)))
    (fromBlocks (updateCol Z (Fin.last n) 0) (ggLastU n) (ggLastU n) (updateCol W (Fin.last n) 0))
  rw [e5, Equiv.Perm.sign_swap (by simp), det_fromBlocks_zero₂₁, ggDet_updateCol_last_single,
    ggDet_updateCol_last_single] at hP
  rw [h1, det_updateCol_add, det_updateCol_smul, e1, e2, h2, det_updateCol_add, det_updateCol_smul,
    e3, e4, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, hW0]
  push_cast at hP
  linear_combination (α * β) * hP

lemma ggDet_keyM (n : ℕ) (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (α β : ℂ) :
    (fromBlocks (α • ggLastU n) Z W (β • ggLastU n)).det =
      (-1) ^ (n + 1) * (Z.det * W.det - α * β * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det) := by
  have h : fromBlocks (α • ggLastU n) Z W (β • ggLastU n) * fromBlocks 0 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 1 0 =
      fromBlocks Z (α • ggLastU n) (β • ggLastU n) W := by
    simp [fromBlocks_multiply]
  have h' := congrArg Matrix.det h
  rw [det_mul, ggDet_swapBlocks, ggDet_keyN] at h'
  have hs : ((-1 : ℂ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination ((-1 : ℂ) ^ (n + 1)) * h' - (fromBlocks (α • ggLastU n) Z W (β • ggLastU n)).det * hs

lemma ggHpk_mulVec_Wb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v)
    (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = (if i.val = r + k then -1 else 1) * v i := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases h : i.val < r ∨ r + k < i.val
    · simp [hv i h]
    · push Not at h
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by first | exact ⟨h.1, h.2, rfl⟩ | exact ⟨h.1, h.2⟩ | simp [h.1, h.2])]
  · intro j _ hji
    by_cases h : j.val < r ∨ r + k < j.val
    · simp [hv j h]
    · push Not at h
      have : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by intro h'; exact hji h'.2.2.symm)]
      simp [this]
  · simp

lemma ggHerm_swap {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H v w = star (herm H w v) := by
  have hH' : ∀ i j, star (H i j) = H j i := by
    intro i j
    have e := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using e
  simp only [herm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, hH',
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

lemma ggHerm_unitary {ι : Type*} [Fintype ι] (H g : Matrix ι ι ℂ) (hg : gᴴ * H * g = H)
    (v w : ι → ℂ) : herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  rw [herm, herm, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

lemma ggHerm_bvec_right {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ)
    (i : ι) : herm H v (Pi.single i 1) = (H *ᵥ v) i := by
  rw [herm]
  have hs : star (Pi.single i (1 : ℂ) : ι → ℂ) = Pi.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [hs]
  first
  | simp [Matrix.single_dotProduct]
  | simp [dotProduct, Pi.single_apply]

lemma ggHpk_ee (k r : ℕ) (a b : Fin r) : Hpk k r (eI k r a) (eI k r b) = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold Hpk
  rw [if_neg (fun h => absurd h.2 (by change ¬ (a.val + b.val = 2 * r + k); omega)),
    if_neg (fun h => absurd h.2 (by change ¬ (a.val + b.val = 2 * r + k); omega)),
    if_neg (fun h => absurd h.1 (by change ¬ (r ≤ a.val); omega))]

lemma ggBlockA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = (herm (Hpk k r) z z • ggLastU r) a b := by
  rw [Matrix.smul_apply, smul_eq_mul]
  have hza : ∀ c : Fin r, (Hpk k r *ᵥ z) (eI k r c) = 0 := by
    intro c
    rw [ggHpk_mulVec_Wb k r z hz, hz _ (Or.inl (by simp [eI])), mul_zero]
  unfold fvec ggLastU
  by_cases ha : a.val < r <;> by_cases hb : b.val < r
  · rw [dif_pos ha, dif_pos hb, if_neg (by intro h; have := congrArg Fin.val h.1; simp at this; omega)]
    simp only [bvec, ggHerm_bvec_right, mulVec_single_one]
    simp [ggHpk_ee]
  · rw [dif_pos ha, dif_neg hb, if_neg (by intro h; have := congrArg Fin.val h.1; simp at this; omega)]
    simp only [bvec, ggHerm_bvec_right, hza, mul_zero]
  · rw [dif_neg ha, dif_pos hb, if_neg (by intro h; have := congrArg Fin.val h.2; simp at this; omega)]
    rw [ggHerm_swap _ (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, hza, star_zero, mul_zero]
  · have hal : a = Fin.last r := Fin.ext (by simp; omega)
    have hbl : b = Fin.last r := Fin.ext (by simp; omega)
    rw [dif_neg ha, dif_neg hb, if_pos ⟨hal, hbl⟩, mul_one]

theorem group_gram_holds : GGram := by
  intro k r z z' hz hz' g hg
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hM : gramM k r z z' g = fromBlocks (herm (Hpk k r) z z • ggLastU r) (Zhat k r z z' g)
      (Zhat k r z z' g)ᴴ (herm (Hpk k r) z' z' • ggLastU r) := by
    ext (a|a) (b|b)
    · exact ggBlockA k r z hz a b
    · rfl
    · show herm (Hpk k r) (fvec k r z b) (g *ᵥ fvec k r z' a) = star (Zhat k r z z' g b a)
      rw [ggHerm_swap _ (GBasic.Hpk_herm k r)]
      rfl
    · show herm (Hpk k r) (g *ᵥ fvec k r z' b) (g *ᵥ fvec k r z' a) = _
      rw [ggHerm_unitary _ _ hg']
      exact ggBlockA k r z' hz' a b
  have hreal : ∀ w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) w w = ((-(Tz k r w) : ℝ) : ℂ) := by
    intro w
    have hc : star (herm (Hpk k r) w w) = herm (Hpk k r) w w :=
      (ggHerm_swap _ (GBasic.Hpk_herm k r) w w).symm
    have h1 : ((herm (Hpk k r) w w).re : ℂ) = herm (Hpk k r) w w := Complex.conj_eq_iff_re.1 hc
    rw [← h1, Tz, neg_neg]
  have hD1 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have hD0 : Dmin k r z z' g ⟨r, by omega⟩ =
      ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  rw [hM, ggDet_keyM, det_conjTranspose, ← conjTranspose_submatrix, det_conjTranspose, ← mul_assoc,
    ← pow_add, Even.neg_one_pow ⟨r + 1, rfl⟩, one_mul, hreal z, hreal z']
  unfold Gf
  rw [hD1, hD0, Complex.star_def, Complex.mul_conj]
  have hc := Complex.mul_conj (((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det)
  push_cast
  linear_combination ((Tz k r z : ℂ) * (Tz k r z' : ℂ)) * hc

lemma ggHerm_Wb (k r : ℕ) (z w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) w z =
      (∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩, star (z i) * w i) -
        star (z ⟨r + k, by omega⟩) * w ⟨r + k, by omega⟩ := by
  simp only [herm, dotProduct, ggHpk_mulVec_Wb k r w hw, Pi.star_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)))]
  have hs : ∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩,
      star (z i) * ((if i.val = r + k then -1 else 1) * w i) =
      ∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩, star (z i) * w i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_neg (fun h => (Finset.ne_of_mem_erase hi) (Fin.ext h)), one_mul]
  rw [hs, if_pos rfl]
  ring

lemma ggRe_star_mul (x : ℂ) : (star x * x).re = ‖x‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  first
  | (simp [Complex.mul_re]; ring)
  | simp [Complex.mul_re]
  | (simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring)

theorem reverse_cauchy_schwarz_holds : RevCS := by
  intro k r z z' hz hz' h1 h2
  have e12 := ggHerm_Wb k r z z' hz'
  have e11 := ggHerm_Wb k r z z hz
  have e22 := ggHerm_Wb k r z' z' hz'
  set L : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩ with hL
  set s := (Finset.univ : Finset (Fin (2 * r + k + 1))).erase L with hs
  set A := ∑ i ∈ s, ‖z i‖ ^ 2 with hA
  set B := ∑ i ∈ s, ‖z' i‖ ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => by positivity)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => by positivity)
  have hre : ∀ w : Fin (2 * r + k + 1) → ℂ, (∑ i ∈ s, star (w i) * w i).re = ∑ i ∈ s, ‖w i‖ ^ 2 := by
    intro w
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => ggRe_star_mul (w i))
  have hzz : (herm (Hpk k r) z z).re = A - ‖z L‖ ^ 2 := by
    rw [e11, Complex.sub_re, hre, ggRe_star_mul]
  have hzz' : (herm (Hpk k r) z' z').re = B - ‖z' L‖ ^ 2 := by
    rw [e22, Complex.sub_re, hre, ggRe_star_mul]
  unfold Tz
  rw [hzz, hzz', e12, Complex.normSq_eq_norm_sq]
  rw [hzz] at h1
  rw [hzz'] at h2
  set S := ∑ i ∈ s, star (z i) * z' i with hS
  set p := ‖z L‖ with hp
  set q := ‖z' L‖ with hq
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  have hSle : ‖S‖ ≤ √A * √B := by
    refine (norm_sum_le _ _).trans ?_
    have := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖z i‖) (fun i => ‖z' i‖)
    simpa [norm_mul] using this
  have hc : ‖star (z L) * z' L‖ = p * q := by simp [norm_mul, hp, hq]
  have hD : p * q - ‖S‖ ≤ ‖S - star (z L) * z' L‖ := by
    rw [norm_sub_rev, ← hc]; exact norm_sub_norm_le _ _
  have ha2 : (√A) ^ 2 = A := Real.sq_sqrt hA0
  have hb2 : (√B) ^ 2 = B := Real.sq_sqrt hB0
  have ha0 : 0 ≤ √A := Real.sqrt_nonneg _
  have hb0 : 0 ≤ √B := Real.sqrt_nonneg _
  have hap : √A < p := by
    by_contra hc'
    push Not at hc'
    nlinarith [mul_le_mul hc' hc' hp0 ha0]
  have hbq : √B < q := by
    by_contra hc'
    push Not at hc'
    nlinarith [mul_le_mul hc' hc' hq0 hb0]
  have h0 : 0 ≤ p * q - √A * √B := by nlinarith [mul_le_mul hap.le hbq.le hb0 hp0]
  have hX : p * q - √A * √B ≤ ‖S - star (z L) * z' L‖ := by linarith
  rw [← ha2, ← hb2]
  nlinarith [mul_self_le_mul_self h0 hX, sq_nonneg (p * √B - q * √A)]

end Formalism.QuantumDeterminants
