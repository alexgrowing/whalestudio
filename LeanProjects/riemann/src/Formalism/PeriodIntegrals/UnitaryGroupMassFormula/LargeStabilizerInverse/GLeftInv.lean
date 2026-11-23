import Formalism.PeriodIntegrals.StabBig
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix

noncomputable section

namespace PI.StabBigW

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem tau_val (i : Fin (2 * r + k + 1)) :
    (tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

theorem wI_val (t : Fin (k + 1)) : (wI k r t).val = r + t.val := rfl

theorem wI_inj {u t : Fin (k + 1)} (h : wI k r u = wI k r t) : u = t := by
  have e := congrArg Fin.val h
  simp only [wI_val] at e
  exact Fin.ext (by omega)

def UT (k r : ℕ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1),
    (j.val ≤ i.val ∨ (r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k)) →
      a i j = if i = j then 1 else 0

theorem hpk_col (m q : Fin (2 * r + k + 1)) :
    Hpk k r m q = if m = tau k r q then sgn k r q else 0 := by
  have ht := tau_val (k := k) (r := r) q
  unfold Hpk sgn
  by_cases hq : q.val < r ∨ r + k < q.val
  · rw [if_pos hq] at ht
    simp only [Fin.ext_iff, ht]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
  · rw [if_neg hq] at ht
    simp only [Fin.ext_iff, ht]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num

private theorem tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have h1 := tau_val (k := k) (r := r) i
  have h2 := tau_val (k := k) (r := r) (tau k r i)
  have hi := i.isLt
  ext
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [if_pos hc] at h1
    have hc2 : (tau k r i).val < r ∨ r + k < (tau k r i).val := by omega
    rw [if_pos hc2] at h2
    omega
  · rw [if_neg hc] at h1
    have hc2 : ¬ ((tau k r i).val < r ∨ r + k < (tau k r i).val) := by omega
    rw [if_neg hc2] at h2
    omega

private theorem sgn_tau' (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  have h1 := tau_val (k := k) (r := r) i
  have hi := i.isLt
  unfold sgn
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [if_pos hc] at h1
    rw [if_neg (by omega : ¬ (tau k r i).val = r + k), if_neg (by omega : ¬ i.val = r + k)]
  · rw [if_neg hc] at h1
    rw [h1]

private theorem Hpk_apply_eq_ite_tau (p m : Fin (2 * r + k + 1)) :
    Hpk k r p m = if m = tau k r p then sgn k r p else 0 := by
  rw [hpk_col]
  by_cases h : m = tau k r p
  · have h2 : p = tau k r m := by rw [h, tau_tau_lemma]
    rw [if_pos h2, if_pos h, h, sgn_tau']
  · have h2 : ¬ p = tau k r m := fun h' => h (by rw [h', tau_tau_lemma])
    rw [if_neg h2, if_neg h]

private theorem Hpk_mul_self' : Hpk k r * Hpk k r = 1 := by
  ext p q
  have e1 : ∀ m, Hpk k r m q = if m = tau k r q then sgn k r q else 0 := fun m => hpk_col m q
  rw [Matrix.mul_apply]
  simp only [e1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hpk_col, tau_tau_lemma, Matrix.one_apply]
  split_ifs with h
  · rw [sgn_tau']
    unfold sgn
    split_ifs <;> norm_num
  · simp

theorem adj_apply (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * aᴴ * Hpk k r) p q = sgn k r p * sgn k r q * star (a (tau k r q) (tau k r p)) := by
  have e1 : ∀ m, Hpk k r m q = if m = tau k r q then sgn k r q else 0 := fun m => hpk_col m q
  have e2 : ∀ m, Hpk k r p m = if m = tau k r p then sgn k r p else 0 := fun m => Hpk_apply_eq_ite_tau p m
  rw [Matrix.mul_apply]
  simp only [e1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Matrix.mul_apply]
  simp only [e2, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Matrix.conjTranspose_apply]
  ring

theorem ut_of_mem {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : UT k r a := by
  unfold Nset at ha
  rw [Set.mem_setOf_eq] at ha
  obtain ⟨hU, hcol, hmid⟩ := ha
  have hU' : aᴴ * Hpk k r * a = Hpk k r := hU
  have hba : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', Hpk_mul_self']
  have hab : a * (Hpk k r * aᴴ * Hpk k r) = 1 := by
    rw [← Matrix.inv_eq_left_inv hba]
    exact Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hba)
  have hcolv : ∀ p m : Fin (2 * r + k + 1), m.val < r → m.val ≤ p.val →
      a p m = if p = m then 1 else 0 := by
    intro p m hm hle
    have e := hcol ⟨m.val, hm⟩ p hle
    rwa [show eI k r ⟨m.val, hm⟩ = m from Fin.ext rfl] at e
  have hsg : ∀ m : Fin (2 * r + k + 1), m.val ≠ r + k → sgn k r m = 1 := by
    intro m hm
    unfold sgn
    rw [if_neg hm]
  have key : ∀ q : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val = q → r + k < q → q ≤ i.val →
      a i j = if i = j then 1 else 0 := by
    intro q
    refine Nat.strong_induction_on q ?_
    intro q IH i j hjq hq hqi
    have hil := i.isLt
    have hjl := j.isLt
    have hj' : j.val < r ∨ r + k < j.val := Or.inr (by omega)
    have htj := tau_val (k := k) (r := r) j
    rw [if_pos hj'] at htj
    have hbjj : (Hpk k r * aᴴ * Hpk k r) j j = 1 := by
      rw [adj_apply, hcolv (tau k r j) (tau k r j) (by omega) le_rfl, if_pos rfl, hsg j (by omega)]
      simp
    have hsum : ∑ m, a i m * (Hpk k r * aᴴ * Hpk k r) m j = a i j := by
      rw [Finset.sum_eq_single j]
      · rw [hbjj, mul_one]
      · intro m _ hmj
        have hml := m.isLt
        by_cases hm1 : m.val ≤ r + k
        · have ha0 : a i m = 0 := by
            by_cases hm2 : m.val < r
            · rw [hcolv i m hm2 (by omega), if_neg (fun h => by have := congrArg Fin.val h; omega)]
            · rw [hmid i m (by omega) hm1 (by omega),
                if_neg (fun h => by have := congrArg Fin.val h; omega)]
          rw [ha0, zero_mul]
        · by_cases hm3 : m.val < j.val
          · rw [IH m.val (by omega) i m rfl (by omega) (by omega),
              if_neg (fun h => by have := congrArg Fin.val h; omega), zero_mul]
          · have hmo : m.val < r ∨ r + k < m.val := Or.inr (by omega)
            have htm := tau_val (k := k) (r := r) m
            rw [if_pos hmo] at htm
            have hmj' : j.val < m.val := by
              rcases Nat.lt_or_ge j.val m.val with h | h
              · exact h
              · exact absurd (Fin.ext (by omega)) hmj
            rw [adj_apply, hcolv (tau k r j) (tau k r m) (by omega) (by omega),
              if_neg (fun h => by have := congrArg Fin.val h; omega)]
            simp only [star_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have E := congrFun (congrFun hab i) j
    rw [Matrix.mul_apply, Matrix.one_apply, hsum] at E
    exact E
  unfold UT
  intro i j hij
  have hil := i.isLt
  have hjl := j.isLt
  by_cases h1 : j.val < r
  · exact hcolv i j h1 (by omega)
  · by_cases h2 : j.val ≤ r + k
    · exact hmid i j (by omega) h2 (by omega)
    · exact key j.val i j rfl (by omega) (by omega)

def dd (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if h : j.val < r then c ⟨j.val, h⟩
  else if h2 : r + k < j.val then (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹ else 0

theorem dd_ne {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) : dd k r c j ≠ 0 := by
  unfold dd
  split_ifs with h1 h2
  · exact hc _
  · exact inv_ne_zero (star_ne_zero.mpr (hc _))
  · exfalso
    omega

theorem dd_tau {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) :
    dd k r (fun a => star (c a)) (tau k r j) * dd k r c j = 1 := by
  have hjl := j.isLt
  have ht := tau_val (k := k) (r := r) j
  rw [if_pos hj] at ht
  rcases hj with h | h
  · have h1 : ¬ (tau k r j).val < r := by omega
    have h2 : r + k < (tau k r j).val := by omega
    have e : (⟨2 * r + k - (tau k r j).val, by omega⟩ : Fin r) = ⟨j.val, h⟩ :=
      Fin.ext (by show 2 * r + k - (tau k r j).val = j.val; omega)
    simp only [dd, dif_neg h1, dif_pos h2, dif_pos h, e, star_star]
    exact inv_mul_cancel₀ (hc _)
  · have h1 : (tau k r j).val < r := by omega
    have h0 : ¬ j.val < r := by omega
    have e : (⟨(tau k r j).val, h1⟩ : Fin r) = ⟨2 * r + k - j.val, by omega⟩ :=
      Fin.ext (by show (tau k r j).val = 2 * r + k - j.val; omega)
    simp only [dd, dif_pos h1, dif_neg h0, dif_pos h, e]
    exact mul_inv_cancel₀ (star_ne_zero.mpr (hc _))

theorem g_col_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    bigCell k r c μ i j = if i = tau k r j then dd k r c j else 0 := by
  have hjl := j.isLt
  have ht := tau_val (k := k) (r := r) j
  rw [if_pos hj] at ht
  rcases hj with h | h
  · have e : esI k r ⟨j.val, h⟩ = tau k r j := Fin.ext (by rw [ht]; rfl)
    simp only [bigCell, dd, dif_pos h, e]
  · have h0 : ¬ j.val < r := by omega
    have h2 : ¬ j.val ≤ r + k := by omega
    simp only [bigCell, dd, dif_neg h0, dif_neg h2, dif_pos h]
    by_cases hi : i = tau k r j
    · have hv : i.val = 2 * r + k - j.val := by rw [hi, ht]
      rw [if_pos hv, if_pos hi]
    · have hv : ¬ i.val = 2 * r + k - j.val := fun h' => hi (Fin.ext (by rw [h', ht]))
      rw [if_neg hv, if_neg hi]

theorem g_mid_col (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k)
    (hi : i.val < r ∨ r + k < i.val) : bigCell k r c μ i j = 0 := by
  have h0 : ¬ j.val < r := by omega
  have h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := by omega
  simp only [bigCell, dif_neg h0, dif_pos hj2, dif_neg h3]

theorem g_wI (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1)) :
    bigCell k r c μ (wI k r s) (wI k r t) = μ s t := by
  have hs := s.isLt
  have ht := t.isLt
  have h1 : ¬ (wI k r t).val < r := by rw [wI_val]; omega
  have h2 : (wI k r t).val ≤ r + k := by rw [wI_val]; omega
  have h3 : r ≤ (wI k r s).val ∧ (wI k r s).val ≤ r + k := by rw [wI_val]; omega
  simp only [bigCell, dif_neg h1, dif_pos h2, dif_pos h3]
  exact congrArg₂ μ (Fin.ext (by show r + s.val - r = s.val; omega))
    (Fin.ext (by show r + t.val - r = t.val; omega))

theorem g_row_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i m : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    bigCell k r c μ i m = if m = tau k r i then dd k r c (tau k r i) else 0 := by
  have hil := i.isLt
  have hml := m.isLt
  have hti := tau_val (k := k) (r := r) i
  rw [if_pos hi] at hti
  by_cases hm : m.val < r ∨ r + k < m.val
  · rw [g_col_out c μ i m hm]
    by_cases h : m = tau k r i
    · have h' : i = tau k r m := by rw [h, tau_tau_lemma]
      rw [if_pos h', if_pos h, h]
    · have h' : ¬ i = tau k r m := fun h'' => h (by rw [h'', tau_tau_lemma])
      rw [if_neg h', if_neg h]
  · have hne : ¬ m = tau k r i := fun h => by have := congrArg Fin.val h; omega
    rw [if_neg hne]
    exact g_mid_col c μ i m (by omega) (by omega) hi

theorem mul_g_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    (A * bigCell k r c μ) i j = A i (tau k r j) * dd k r c j := by
  have hcol : ∀ m, bigCell k r c μ m j = if m = tau k r j then dd k r c j else 0 :=
    fun m => g_col_out c μ m j hj
  rw [Matrix.mul_apply]
  simp only [hcol, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem g_mul_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (bigCell k r c μ * B) i j = dd k r c (tau k r i) * B (tau k r i) j := by
  have hrow : ∀ m, bigCell k r c μ i m = if m = tau k r i then dd k r c (tau k r i) else 0 :=
    fun m => g_row_out c μ i m hi
  rw [Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem sum_mid (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ m : Fin (2 * r + k + 1), (m.val < r ∨ r + k < m.val) → f m = 0) :
    ∑ m, f m = ∑ s : Fin (k + 1), f (wI k r s) := by
  have himg : ∑ s : Fin (k + 1), f (wI k r s) = ∑ m ∈ Finset.univ.image (wI k r), f m :=
    (Finset.sum_image (fun u _ t _ h => wI_inj h)).symm
  rw [himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  apply hf
  by_contra hc
  apply hm
  have hml := m.isLt
  rw [Finset.mem_image]
  refine ⟨⟨m.val - r, by omega⟩, Finset.mem_univ _, ?_⟩
  ext
  simp only [wI_val]
  omega

theorem mul_g_mid (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    (A * bigCell k r c μ) i (wI k r t) = ∑ s, A i (wI k r s) * μ s t := by
  have htl := t.isLt
  rw [Matrix.mul_apply, sum_mid]
  · simp only [g_wI]
  · intro m hm
    rw [g_mid_col c μ m (wI k r t) (by rw [wI_val]; omega) (by rw [wI_val]; omega) hm, mul_zero]

theorem hb_sq : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem vec_zero {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μ * L = 1)
    (v : Fin (k + 1) → ℂ) (hv : ∀ t, ∑ s, v s * μ s t = 0) : v = 0 := by
  have h1 : Matrix.vecMul v μ = 0 := by
    funext t
    rw [Pi.zero_apply, ← hv t]
    rfl
  calc v = Matrix.vecMul v (μ * L) := by rw [h, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul v μ) L := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

theorem g_left_inv {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hL : L * μ = 1) : bigCell k r (fun a => star (c a)) L * bigCell k r c μ = 1 := by
  ext i j
  rw [Matrix.one_apply]
  have hil := i.isLt
  have hjl := j.isLt
  by_cases hj : j.val < r ∨ r + k < j.val
  · have ht := tau_val (k := k) (r := r) j
    rw [if_pos hj] at ht
    have hto : (tau k r j).val < r ∨ r + k < (tau k r j).val := by omega
    rw [mul_g_out _ _ _ i j hj, g_col_out _ _ i (tau k r j) hto, tau_tau_lemma, ite_mul, zero_mul,
      dd_tau hc j hj]
  · have ej : j = wI k r ⟨j.val - r, by omega⟩ := Fin.ext (by simp only [wI_val]; omega)
    rw [ej, mul_g_mid]
    by_cases hi : i.val < r ∨ r + k < i.val
    · have hne : ¬ i = wI k r ⟨j.val - r, by omega⟩ := fun h => by
        have e := congrArg Fin.val h
        simp only [wI_val] at e
        omega
      rw [if_neg hne]
      apply Finset.sum_eq_zero
      intro s _
      have hs := s.isLt
      rw [g_mid_col _ _ i _ (by simp only [wI_val]; omega) (by simp only [wI_val]; omega) hi, zero_mul]
    · have ei : i = wI k r ⟨i.val - r, by omega⟩ := Fin.ext (by simp only [wI_val]; omega)
      rw [ei]
      simp only [g_wI]
      rw [← Matrix.mul_apply, hL, Matrix.one_apply]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (by rw [h1]) h2
      · exact absurd (wI_inj h2) h1
      · rfl

theorem eq_one_of {c : Fin r → ℂ} {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hc : ∀ a, c a ≠ 0) (hL : μ * L = 1)
    {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : UT k r a) (hb : UT k r b) (E : a * bigCell k r c μ = bigCell k r c μ * b) : a = 1 := by
  ext i m
  rw [Matrix.one_apply]
  have hil := i.isLt
  have hml := m.isLt
  by_cases hmi : m.val ≤ i.val ∨ (r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ m.val ∧ m.val ≤ r + k)
  · exact ha i m hmi
  have hne : ¬ i = m := fun h => hmi (Or.inl (by subst h; exact le_refl _))
  rw [if_neg hne]
  by_cases hm : m.val < r ∨ r + k < m.val
  · have htm := tau_val (k := k) (r := r) m
    rw [if_pos hm] at htm
    have hjo : (tau k r m).val < r ∨ r + k < (tau k r m).val := by omega
    have E1 := congrFun (congrFun E i) (tau k r m)
    rw [mul_g_out _ _ _ i _ hjo, tau_tau_lemma] at E1
    have hd := dd_ne hc (tau k r m) hjo
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [g_mul_out _ _ _ i _ hi] at E1
      have hti := tau_val (k := k) (r := r) i
      rw [if_pos hi] at hti
      have hb0 : b (tau k r i) (tau k r m) = 0 := by
        rw [hb (tau k r i) (tau k r m) (Or.inl (by omega)),
          if_neg (fun h => by have := congrArg Fin.val h; omega)]
      rw [hb0, mul_zero] at E1
      exact (mul_eq_zero.mp E1).resolve_right hd
    · rw [Matrix.mul_apply] at E1
      have hz : ∑ n, bigCell k r c μ i n * b n (tau k r m) = 0 := by
        apply Finset.sum_eq_zero
        intro n _
        have hnl := n.isLt
        by_cases hn : n.val < r ∨ r + k < n.val
        · have htn := tau_val (k := k) (r := r) n
          rw [if_pos hn] at htn
          have hin : ¬ i = tau k r n := fun h => by have := congrArg Fin.val h; omega
          rw [g_col_out _ _ i n hn, if_neg hin, zero_mul]
        · rw [hb n (tau k r m) (Or.inl (by omega)),
            if_neg (fun h => by have := congrArg Fin.val h; omega), mul_zero]
      rw [hz] at E1
      exact (mul_eq_zero.mp E1).resolve_right hd
  · have hi : i.val < r ∨ r + k < i.val := by omega
    have emw : m = wI k r ⟨m.val - r, by omega⟩ := Fin.ext (by simp only [wI_val]; omega)
    have hti := tau_val (k := k) (r := r) i
    rw [if_pos hi] at hti
    have hv : (fun s => a i (wI k r s)) = 0 := by
      apply vec_zero hL
      intro t
      have htl := t.isLt
      show ∑ s, a i (wI k r s) * μ s t = 0
      have E1 := congrFun (congrFun E i) (wI k r t)
      rw [mul_g_mid, g_mul_out _ _ _ i _ hi] at E1
      rw [E1, hb (tau k r i) (wI k r t) (Or.inl (by simp only [wI_val]; omega)),
        if_neg (fun h => by
          have e := congrArg Fin.val h
          simp only [wI_val] at e
          omega), mul_zero]
    rw [emw]
    exact congrFun hv _

theorem stabBig : PI.StabBig := by
  intro k r c μ hc hμ
  have hL : (Hb k * μᴴ * Hb k) * μ = 1 := by
    calc (Hb k * μᴴ * Hb k) * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμ, hb_sq]
  have hR : μ * (Hb k * μᴴ * Hb k) = 1 := by
    rw [← Matrix.inv_eq_left_inv hL]
    exact Matrix.mul_nonsing_inv μ (Matrix.isUnit_det_of_left_inverse hL)
  have hG : bigCell k r (fun a => star (c a)) (Hb k * μᴴ * Hb k) * bigCell k r c μ = 1 :=
    g_left_inv hc hL
  have hdet : IsUnit (bigCell k r c μ).det := Matrix.isUnit_det_of_left_inverse hG
  have hGr : bigCell k r c μ * (bigCell k r c μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1N : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r := by
    unfold Nset UH
    simp [Matrix.one_apply]
  ext a
  simp only [RStab, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hb⟩
    have E : a * bigCell k r c μ =
        bigCell k r c μ * ((bigCell k r c μ)⁻¹ * a * bigCell k r c μ) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGr, Matrix.one_mul]
    exact eq_one_of hc hR (ut_of_mem ha) (ut_of_mem hb) E
  · rintro rfl
    refine ⟨h1N, ?_⟩
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hdet]
    exact h1N

end PI.StabBigW
