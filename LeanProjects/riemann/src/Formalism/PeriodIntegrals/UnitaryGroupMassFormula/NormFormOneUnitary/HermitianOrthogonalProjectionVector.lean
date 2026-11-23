import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP

open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

noncomputable section

namespace NFOne

def Vv {k r j : ℕ} (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ) (c : ℕ) :
    Fin (2 * r + k + 1) → ℂ := if h : c < j then ∑ a, N ⟨c, h⟩ a • y a else 0

private theorem herm_sum_smul_left' {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ a, α a • v a) w = ∑ a, α a * herm H (v a) w := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => by ring

private theorem herm_sum_smul_right' {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} [Fintype ι]
    (β : ι → ℂ) (v : Fin n → ℂ) (w : ι → Fin n → ℂ) :
    herm H v (∑ a, β a • w a) = ∑ a, star (β a) * herm H v (w a) := by
  unfold herm
  simp only [dotProduct, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem herm_comb (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hyy : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (α β : Fin j → ℂ) :
    herm (Hpk k r) (∑ a, α a • y a) (∑ a, β a • y a) = 0 := by
  rw [herm_sum_smul_left']
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [herm_sum_smul_right']
  simp [hyy]

theorem herm_Hpk_of_inWb_eq_sum_wI (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (β : Fin j → ℂ) :
    herm (Hpk k r) z' (∑ a, β a • y a) = 0 := by
  rw [herm_sum_smul_right']
  simp [hzy]

theorem Vv_zero {k r j : ℕ} (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (c : ℕ) (hc : j ≤ c) : Vv y N c = 0 := by
  unfold Vv
  rw [dif_neg (by omega)]

theorem Vv_iso (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (hyy : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (b c : ℕ) (hb : b < j) (hc : c < j) :
    herm (Hpk k r) (Vv y N b) (Vv y N c) = 0 := by
  unfold Vv
  rw [dif_pos hb, dif_pos hc]
  exact herm_comb k r j y hyy _ _

theorem hermitian_orthogonal_projection_vector (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (z' : Fin (2 * r + k + 1) → ℂ) (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (c : ℕ) :
    herm (Hpk k r) z' (Vv y N c) = 0 := by
  unfold Vv
  split_ifs with h
  · exact herm_Hpk_of_inWb_eq_sum_wI k r j y z' hzy _
  · simp [herm]

theorem y_esI_zero (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (a : Fin j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) (hb : ¬ (sg k r q).val < j) :
    y a q = 0 := by
  have hq2 := q.isLt
  have hb' : (sg k r q).val < r := by simp only [sg_val]; omega
  have h := hy2 a ⟨(sg k r q).val, hb'⟩ (Nat.le_of_not_lt hb)
  have he : esI k r ⟨(sg k r q).val, hb'⟩ = q := by
    apply Fin.ext
    simp only [esI, sg_val]
    omega
  rw [he] at h
  exact h

theorem projection_vector_coordinate (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hNM : N * (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) = 1)
    (b : ℕ) (hb : b < j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    Vv y N b q = if (sg k r q).val = b then 1 else 0 := by
  have hq2 := q.isLt
  unfold Vv
  rw [dif_pos hb]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hs : (sg k r q).val < j
  · have hsr : sR k r j hj ⟨(sg k r q).val, hs⟩ = q := by
      apply Fin.ext
      show 2 * r + k - (sg k r q).val = q.val
      simp only [sg_val]
      omega
    have h := congrFun (congrFun hNM ⟨b, hb⟩) ⟨(sg k r q).val, hs⟩
    rw [Matrix.mul_apply] at h
    simp only [Matrix.of_apply, hsr, Matrix.one_apply, Fin.ext_iff] at h
    rw [h]
    split_ifs <;> first | rfl | (exfalso; omega)
  · have h0 : ∀ a, y a q = 0 := fun a => y_esI_zero k r j y hy2 a q hq hs
    simp only [h0, mul_zero, Finset.sum_const_zero]
    rw [if_neg (by omega)]

theorem nf_sum (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) * N = 1)
    (a : Fin j) (p : Fin (2 * r + k + 1)) :
    (Pm k r j (Vv y N) *ᵥ (fun q => if r + k < q.val then y a q else 0)) p =
      if r + k < p.val then 0 else y a p := by
  have hp2 := p.isLt
  have hsRv : ∀ l : Fin j, (sR k r j hj l).val = 2 * r + k - l.val := fun l => rfl
  rw [show (Pm k r j (Vv y N) *ᵥ (fun q => if r + k < q.val then y a q else 0)) p =
    ∑ q, Pm k r j (Vv y N) p q * (if r + k < q.val then y a q else 0) from rfl]
  split_ifs with hp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [P_rowS k r j _ p q hp, zero_mul]
  · have key : ∀ q : Fin (2 * r + k + 1),
        Pm k r j (Vv y N) p q * (if r + k < q.val then y a q else 0) =
          if r + k < q.val ∧ (sg k r q).val < j then Vv y N (sg k r q).val p * y a q else 0 := by
      intro q
      by_cases hq : r + k < q.val
      · rw [if_pos hq]
        by_cases hs : (sg k r q).val < j
        · rw [if_pos ⟨hq, hs⟩]
          congr 1
          by_cases hpr : p.val < r
          · rw [P_XS k r j _ p q hpr hq, if_pos hs]
          · exact P_WS k r j _ p q (by omega) (by omega) hq
        · rw [if_neg (fun h => hs h.2), y_esI_zero k r j y hy2 a q hq hs, mul_zero]
      · rw [if_neg hq, mul_zero, if_neg (fun h => hq h.1)]
    simp only [key]
    have hinj : Function.Injective (sR k r j hj) := by
      intro l1 l2 h
      have h' := congrArg Fin.val h
      rw [hsRv, hsRv] at h'
      have := l1.isLt
      have := l2.isLt
      exact Fin.ext (by omega)
    have hzero : ∀ q ∉ Set.range (sR k r j hj),
        (if r + k < q.val ∧ (sg k r q).val < j then Vv y N (sg k r q).val p * y a q else 0) = 0 := by
      intro q hq
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hq
      refine ⟨⟨(sg k r q).val, h2⟩, Fin.ext ?_⟩
      rw [hsRv]
      have := q.isLt
      simp only [sg_val]
      omega
    have hval : ∀ l : Fin j, Vv y N l.val p * y a (sR k r j hj l) =
        (if r + k < (sR k r j hj l).val ∧ (sg k r (sR k r j hj l)).val < j then
          Vv y N (sg k r (sR k r j hj l)).val p * y a (sR k r j hj l) else 0) := by
      intro l
      have hl := l.isLt
      have e : (sg k r (sR k r j hj l)).val = l.val := by rw [sg_val, hsRv]; omega
      rw [if_pos ⟨by rw [hsRv]; omega, by omega⟩, e]
    rw [← Fintype.sum_of_injective (sR k r j hj) hinj _ _ hzero hval]
    have hV : ∀ l : Fin j, Vv y N l.val p = ∑ a', N l a' * y a' p := by
      intro l
      unfold Vv
      rw [dif_pos l.isLt]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.eta]
    simp only [hV]
    have h1 : y a p = ∑ a', (∑ l, y a (sR k r j hj l) * N l a') * y a' p := by
      have := fun a' => congrFun (congrFun hMN a) a'
      simp only [Matrix.mul_apply, Matrix.of_apply] at this
      simp only [this, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [h1]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun l _ => by ring

theorem nf (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) * N = 1) (a : Fin j) :
    (1 + Pm k r j (Vv y N)) *ᵥ (fun q => if r + k < q.val then y a q else 0) = y a := by
  funext p
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, nf_sum k r j hj y N hy2 hMN a p]
  split_ifs <;> simp

theorem cols_X (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (1 + Pm k r j V) *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  funext p
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  have h : (Pm k r j V *ᵥ bvec (eI k r a)) p = 0 := by
    rw [show (Pm k r j V *ᵥ bvec (eI k r a)) p = ∑ q, Pm k r j V p q * bvec (eI k r a) q from rfl]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : q = eI k r a
    · subst hq
      rw [P_colX k r j V p _ a.isLt, zero_mul]
    · simp [bvec, Pi.single_apply, hq]
  rw [h, add_zero]

theorem z_fix (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + Pm k r j V) *ᵥ z' = z' := by
  funext p
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  suffices h : (Pm k r j V *ᵥ z') p = 0 by rw [h, add_zero]
  have hterm : ∀ q : Fin (2 * r + k + 1), Pm k r j V p q * z' q =
      if p.val < r then -(star (V p.val q) * (Hpk k r *ᵥ z') q) else 0 := by
    intro q
    have hq2 := q.isLt
    by_cases hW : r ≤ q.val ∧ q.val ≤ r + k
    · rw [Hpk_mulVec, if_pos hW]
      by_cases hp : p.val < r
      · rw [P_XW k r j V p q hp hW.1 hW.2, if_pos hp]
        ring
      · rw [P_rowWS_colW k r j V p q (by omega) hW.2, if_neg hp, zero_mul]
    · have hzq : z' q = 0 := hz q (by omega)
      have hz2 : z' (sg k r q) = 0 := hz (sg k r q) (by simp only [sg_val]; omega)
      rw [hzq, mul_zero, Hpk_mulVec, if_neg hW, hz2, mul_zero, neg_zero, ite_self]
  rw [show (Pm k r j V *ᵥ z') p = ∑ q, Pm k r j V p q * z' q from rfl]
  simp only [hterm]
  by_cases hp : p.val < r
  · simp only [if_pos hp, Finset.sum_neg_distrib, neg_eq_zero]
    have := Vz p.val
    rw [herm_eq] at this
    exact this
  · simp [if_neg hp]

theorem normFormOne : IsotropicNormalFormPartial := by
  intro k r z' j hj y hz hy2 hdet hzy hyy
  have hu : IsUnit (Matrix.of fun a b : Fin j => y a (sR k r j hj b)).det := isUnit_iff_ne_zero.mpr hdet
  have hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) *
      (Matrix.of fun a b : Fin j => y a (sR k r j hj b))⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hNM : (Matrix.of fun a b : Fin j => y a (sR k r j hj b))⁻¹ *
      (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨1 + Pm k r j (Vv y (Matrix.of fun a b : Fin j => y a (sR k r j hj b))⁻¹), ?_,
    fun a q => if r + k < q.val then y a q else 0, fun a => ⟨?_, ?_, ?_⟩⟩
  · simp only [N0set, UH, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact unitary_P k r j _ (fun c hc => Vv_zero y _ c hc)
        (fun b hb q hq => projection_vector_coordinate k r j hj y _ hy2 hNM b hb q hq)
        (fun b c hb hc => Vv_iso k r j y _ hyy b c hb hc)
    · exact fun a => cols_X k r j _ a
    · exact z_fix k r j _ z' hz (fun c => hermitian_orthogonal_projection_vector k r j y _ z' hzy c)
    · intro p q hq1 hq2 hp
      rw [Matrix.add_apply, P_rowWS_colW k r j _ p q hp hq2, add_zero, Matrix.one_apply]
    · intro p q hq hp
      rw [Matrix.add_apply, P_rowS k r j _ p q hp, add_zero, Matrix.one_apply]
  · exact nf k r j hj y _ hy2 hMN a
  · intro p hp
    exact if_neg (show ¬ (r + k < p.val) by omega)
  · intro p hp
    exact if_pos hp

end NFOne
