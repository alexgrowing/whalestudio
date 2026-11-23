import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.OldestLetterInSegment

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

open Classical in

def LeadingLetterInAtMostTwoSegments : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ t : Fin n',
    ∑ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤ 2

section locP_coef_Lsh

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem oldest_le_row (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    X.F.oldest j x ≤ X.row j x i := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  have hi := i.isLt
  rw [oldest_eq, row_eq]
  have h1 : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  exact evL_mono X.F j x (by omega) h2

theorem sg_mul_le (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    (X.sg p K j x : ℝ) * (p : ℝ) ^ X.F.dist j (X.row j x i) ≤ 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  have hold : X.F.oldest j x ∈ X.F.letters j := by
    rw [oldest_eq]
    have h1 : (evL X.F j x).length - r < (evL X.F j x).length := by omega
    rw [List.getD_eq_getElem _ _ h1]
    exact ((mem_evL X.F j x _).1 (List.getElem_mem h1)).1
  have hle := oldest_le_row hX j x hx i
  have hdist : X.F.dist j (X.row j x i) ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  obtain ⟨-, -, hpos⟩ := mem_letters_bounds hold
  have hdeg := (hX.degs _ hpos).2
  have hp1 : 1 ≤ p := le_trans (by norm_num) hX.p13
  have hp : (1:ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0:ℝ) < p := by linarith
  have hK0 : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hkpos : (0:ℝ) < Dat.k (r := r) K := by
    unfold Dat.k
    exact_mod_cast (by omega : 0 < r + K)
  have hY := hX.Y1
  have hk : 0 < Dat.k (r := r) K ^ 2 * X.Y := by positivity
  have hpd : (0:ℝ) < (p:ℝ) ^ X.F.dist j (X.F.oldest j x) := pow_pos hp0 _
  have hBo : 0 ≤ X.Bo p j x := by
    unfold Dat.Bo
    exact div_nonneg (Nat.cast_nonneg _) hpd.le
  have hsg : (X.sg p K j x : ℝ) ≤ X.Bo p j x / (Dat.k (r := r) K ^ 2 * X.Y) := by
    unfold Dat.sg
    exact Nat.floor_le (div_nonneg hBo hk.le)
  have hpow : (p:ℝ) ^ X.F.dist j (X.row j x i) ≤ (p:ℝ) ^ X.F.dist j (X.F.oldest j x) :=
    pow_le_pow_right₀ hp hdist
  calc (X.sg p K j x : ℝ) * (p:ℝ) ^ X.F.dist j (X.row j x i)
      ≤ X.Bo p j x / (Dat.k (r := r) K ^ 2 * X.Y) * (p:ℝ) ^ X.F.dist j (X.F.oldest j x) :=
        mul_le_mul hsg hpow (by positivity) (div_nonneg hBo hk.le)
    _ = (X.deg (posOf n' (X.F.oldest j x)) : ℝ) / (Dat.k (r := r) K ^ 2 * X.Y) := by
        unfold Dat.Bo
        field_simp
    _ ≤ 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
        gcongr

private theorem late_index_map_mem_letters (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    X.row j x i ∈ X.F.letters j := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  have hi := i.isLt
  rw [row_eq]
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h2]
  exact ((mem_evL X.F j x _).1 (List.getElem_mem h2)).1

private theorem late_index_map_injective (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) :
    Function.Injective (X.row j x) := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  intro i i' h
  have hi := i.isLt
  have hi' := i'.isLt
  rw [row_eq, row_eq] at h
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  have h2' : (evL X.F j x).length - r + (i' : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h2'] at h
  have h3 := (evL_nodup X.F j x).getElem_inj_iff.1 h
  ext
  omega

open Classical in
theorem Et_le (hOcc : LeadingLetterInAtMostTwoSegments) (hX : X.Hyp p K) (t : Fin n') :
    (X.Et p K t : ℝ) ≤ 4 * (X.Ns : ℝ) * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
  have B := basics hX
  have hY0 : 0 ≤ X.Y := by linarith [B.Y1]
  have hlhs : 0 ≤ (32:ℝ) * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) hY0) (sq_nonneg _)) (Nat.cast_nonneg _)) (sq_nonneg _)) (by positivity)
  have ha0 : 0 ≤ X.a := le_trans hlhs hX.P3
  have hk5 := B.k5
  have hden : 0 < Dat.k (r := r) K ^ 2 * X.Y := by
    have : (0:ℝ) < Dat.k (r := r) K := by linarith
    have : (0:ℝ) < X.Y := by linarith [B.Y1]
    positivity
  set c : ℝ := 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hden.le
  have hcnt : ∀ j : ℤ, ∀ x ∈ X.toLate j,
      (Finset.univ.filter fun i : Fin r => posOf n' (X.row j x i) = t).card ≤
        ((X.F.letters j).filter fun y => posOf n' y = t).card := by
    intro j x hx
    apply Finset.card_le_card_of_injOn (fun i => X.row j x i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        Finset.mem_coe, Finset.mem_filter] at hi ⊢
      exact ⟨late_index_map_mem_letters hX j x hx i, hi⟩
    · intro i _ i' _ h
      exact late_index_map_injective hX j x hx h
  have hterm : ∀ j : ℤ, ∀ x ∈ X.toLate j,
      (((X.sg p K j x * ∑ i : Fin r, if posOf n' (X.row j x i) = t then p ^ X.F.dist j (X.row j x i) else 0 : ℕ)) : ℝ)
        ≤ c * (((X.F.letters j).filter fun y => posOf n' y = t).card : ℝ) := by
    intro j x hx
    push_cast
    rw [Finset.mul_sum]
    calc ∑ i : Fin r, (X.sg p K j x : ℝ) *
          (if posOf n' (X.row j x i) = t then (p : ℝ) ^ X.F.dist j (X.row j x i) else 0)
        ≤ ∑ i : Fin r, (if posOf n' (X.row j x i) = t then c else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact sg_mul_le hX j x hx i
          · simp
      _ = c * ((Finset.univ.filter fun i : Fin r => posOf n' (X.row j x i) = t).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := by
          gcongr
          exact_mod_cast hcnt j x hx
  have hOcc' := hOcc p n' r K X hX t
  have hOccR : (∑ j ∈ Finset.range X.F.J,
      (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) ≤ 2 := by
    exact_mod_cast hOcc'
  unfold Dat.Et
  rw [Nat.cast_sum]
  calc _ ≤ ∑ j ∈ Finset.range X.F.J,
        (X.Ns : ℝ) * (c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Nat.cast_sum]
        calc _ ≤ ∑ x ∈ X.toLate (j : ℤ),
              c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ) :=
              Finset.sum_le_sum fun x hx => hterm _ x hx
          _ = ((X.toLate (j : ℤ)).card : ℝ) *
              (c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by
              have hl : (X.toLate (j : ℤ)).card ≤ X.Ns := (Finset.card_filter_le _ _).trans (hX.card _)
              gcongr
    _ = (X.Ns : ℝ) * (c * ∑ j ∈ Finset.range X.F.J,
          (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (X.Ns : ℝ) * (c * 2) := by gcongr
    _ = 4 * (X.Ns : ℝ) * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
        rw [hc]
        ring

theorem a_ge (hX : X.Hyp p K) : 32 * ((X.E₀ : ℝ) + X.mStar + 1) ≤ X.a := by
  have B := basics hX
  have hE : (0:ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by positivity
  have hrK : (1:ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h := B.k5
    unfold Dat.k at h
    linarith
  have hsq : (1:ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := one_le_pow₀ hrK
  have hq : (1:ℝ) ≤ X.Q ^ 2 := one_le_pow₀ B.Q1
  have hp : (1:ℝ) ≤ p := by linarith [B.p1]
  have hY := B.Y1
  have hNs := B.Ns1
  have h1 : (1:ℝ) ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 := by
    have e1 : (1:ℝ) ≤ (p : ℝ) * X.Y := one_le_mul_of_one_le_of_one_le hp hY
    have e2 := one_le_mul_of_one_le_of_one_le e1 hsq
    have e3 := one_le_mul_of_one_le_of_one_le e2 hNs
    exact one_le_mul_of_one_le_of_one_le e3 hq
  have h2 := mul_le_mul_of_nonneg_right h1 hE
  have h3 := hX.P3
  nlinarith

theorem k_sq_mul_Y_ge_Ns (hX : X.Hyp p K) (hC : 32 ≤ X.Ck) : 160 * (X.Ns : ℝ) ≤ Dat.k (r := r) K ^ 2 * X.Y := by
  have B := basics hX
  have ha := a_ge hX
  have hE0 : (0:ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have ha32 : (32:ℝ) ≤ X.a := by linarith
  have hlog : 1 ≤ Real.log X.a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hNs := B.Ns1
  have hNs2 : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    have e1 : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by nlinarith
    have e2 : (X.Ns : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a :=
      le_mul_of_one_le_right (sq_nonneg _) hlog
    linarith
  have hCk : 32 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.Ck * (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    rw [mul_assoc X.Ck]
    exact mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
  have hP1 := hX.P1
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hk5 : (5:ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h := B.k5
    rw [hkdef] at h
    exact h
  have hk32 : 32 * (X.Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) := by linarith
  have hY := hX.Y1
  rw [hkdef]
  have e1 : 0 ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Y - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have e2 : 0 ≤ ((r + K : ℕ) : ℝ) * (((r + K : ℕ) : ℝ) - 5) := mul_nonneg (by linarith) (by linarith)
  nlinarith

end locP_coef_Lsh

theorem top_count_lower_bounds_of_occurrence (C₀ : ℝ) (hC : 32 ≤ C₀) (hOcc : LeadingLetterInAtMostTwoSegments) : TopCountLowerBounds C₀ := by
  intro p n' r K _ _ _ X hX _ hCk
  have hCk' : 32 ≤ X.Ck := le_trans hC hCk
  have hk := k_sq_mul_Y_ge_Ns hX hCk'
  have ha := a_ge hX
  have B := basics hX
  have hNs : (1:ℝ) ≤ X.Ns := B.Ns1
  have hE0 : (0:ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have ha0 : 0 ≤ X.a := by linarith
  have hE0a : 32 * (X.E₀ : ℝ) ≤ X.a := by linarith
  have hEt40 : ∀ t, (X.Et p K t : ℝ) ≤ X.a / 40 := by
    intro t
    refine (Et_le hOcc hX t).trans ?_
    have hpos : 0 < Dat.k (r := r) K ^ 2 * X.Y := by linarith
    rw [div_le_div_iff₀ hpos (by norm_num)]
    have := mul_le_mul_of_nonneg_left hk ha0
    nlinarith
  have hd : ∀ t ∈ X.F.TT, (X.d t : ℝ) = X.deg t - X.E' t := by
    intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    have hle : X.E' t ≤ X.deg t := by
      have : (X.E' t : ℝ) ≤ X.deg t := by linarith
      exact_mod_cast this
    unfold Dat.d
    rw [if_pos ht, Nat.cast_sub hle]
  have hEtd : ∀ t ∈ X.F.TT, X.Et p K t ≤ X.d t := by
    intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    have h : (X.Et p K t : ℝ) ≤ X.d t := by
      rw [hd t ht]
      linarith [hEt40 t]
    exact_mod_cast h
  constructor
  · intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    unfold Dat.a'
    rw [Nat.cast_sub (hEtd t ht), hd t ht]
    linarith [hEt40 t]
  · intro t
    by_cases ht : t ∈ X.F.TT
    · exact hEtd t ht
    · have h0 : X.Et p K t = 0 := by
        unfold Dat.Et
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro x hx
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro hpos
        apply ht
        rw [← hpos]
        exact (mem_letters_bounds (late_index_map_mem_letters hX _ x hx i)).2.2
      rw [h0]
      exact Nat.zero_le _

end Formalism.MainNotions.SelectionLemmas.Pf
