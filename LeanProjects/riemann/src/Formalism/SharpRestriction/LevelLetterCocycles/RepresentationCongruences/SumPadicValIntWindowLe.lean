import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsSumPadicValIntWindowEq

noncomputable section

open Classical Finset

namespace Formalism.MainNotions.N.Ln17

theorem padicValNat_eq_card_dvd_pows (l : ℕ) (hl : 2 ≤ l) (N b : ℕ) (hN : N ≠ 0) (hb : N < l ^ b) :
    padicValNat l N = ((Ico 1 b).filter (fun i => l ^ i ∣ N)).card := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have key : ∀ i, l ^ i ∣ N ↔ i ≤ padicValNat l N := by
    intro i
    have hfin : FiniteMultiplicity l N := Nat.finiteMultiplicity_iff.2 ⟨by omega, hN0⟩
    rw [padicValNat_def' (by omega) hN]
    exact hfin.pow_dvd_iff_le_multiplicity
  have hv : padicValNat l N < b := by
    have h1 : l ^ padicValNat l N ≤ N := Nat.le_of_dvd hN0 ((key _).2 le_rfl)
    by_contra hc
    push_neg at hc
    have : l ^ b ≤ l ^ padicValNat l N := Nat.pow_le_pow_right (by omega) hc
    omega
  have hset : (Ico 1 b).filter (fun i => l ^ i ∣ N) = Icc 1 (padicValNat l N) := by
    ext i
    simp only [mem_filter, mem_Ico, mem_Icc, key]
    omega
  rw [hset, Nat.card_Icc]
  omega

theorem sum_padicVal_window_split (l : ℕ) (hl : 2 ≤ l) (m b : ℕ) :
    ∀ S : ℕ, m + S < l ^ b →
      (∑ j ∈ range S, padicValNat l (m + 1 + j)) + ∑ i ∈ Ico 1 b, m / l ^ i =
        ∑ i ∈ Ico 1 b, (m + S) / l ^ i := by
  intro S
  induction S with
  | zero => intro _; simp
  | succ S ih =>
    intro hS
    have ih' := ih (by omega)
    rw [sum_range_succ]
    have hv := padicValNat_eq_card_dvd_pows l hl (m + 1 + S) b (by omega) (by omega)
    have hdiv : ∀ i, (m + (S + 1)) / l ^ i =
        (m + S) / l ^ i + if l ^ i ∣ m + 1 + S then 1 else 0 := by
      intro i
      rw [show m + (S + 1) = m + S + 1 by omega, Nat.succ_div, show m + S + 1 = m + 1 + S by omega]
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), sum_add_distrib, sum_boole, Nat.cast_id]
    omega

theorem sum_padicVal_window_le (l : ℕ) (hl : 2 ≤ l) (m S : ℕ) :
    ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + Real.logb l ((m + S : ℕ) : ℝ) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hlpos : (0:ℝ) < (l:ℝ) - 1 := by linarith
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_div, zero_add, add_zero]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact Real.logb_nonneg hl1 (by exact_mod_cast h0)
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.log l (m + S) + 1 := ⟨_, rfl⟩
  have hlt : m + S < l ^ b := by rw [hb]; exact Nat.lt_pow_succ_log_self (by omega) _
  have E := sum_padicVal_window_split l hl m b S hlt
  have hT : ∑ i ∈ Ico 1 b, (m + S) / l ^ i ≤ ∑ i ∈ Ico 1 b, (m / l ^ i + (S / l ^ i + 1)) := by
    apply Finset.sum_le_sum
    intro i _
    have hq : 0 < l ^ i := by positivity
    rw [Nat.add_div hq]
    split_ifs <;> omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at hT
  have hN : ∑ j ∈ range S, padicValNat l (m + 1 + j) ≤ ∑ i ∈ Ico 1 b, S / l ^ i + (b - 1) := by omega
  have hgeo : ((∑ i ∈ Ico 1 b, S / l ^ i : ℕ) : ℝ) ≤ S / ((l:ℝ) - 1) := by
    rw [Nat.cast_sum]
    calc ∑ i ∈ Ico 1 b, ((S / l ^ i : ℕ) : ℝ) ≤ ∑ i ∈ Ico 1 b, (S:ℝ) * (1 / (l:ℝ)) ^ i := by
          apply Finset.sum_le_sum
          intro i _
          rw [one_div, inv_pow, ← div_eq_mul_inv]
          calc ((S / l ^ i : ℕ) : ℝ) ≤ (S:ℝ) / ((l ^ i : ℕ) : ℝ) := Nat.cast_div_le
            _ = (S:ℝ) / (l:ℝ) ^ i := by push_cast; rfl
      _ = S * ∑ i ∈ Ico 1 b, (1 / (l:ℝ)) ^ i := by rw [Finset.mul_sum]
      _ ≤ S * ((1 / (l:ℝ)) ^ 1 / (1 - 1 / (l:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply geom_sum_Ico_le_of_lt_one (by positivity)
          rw [div_lt_one (by linarith)]
          exact hl1
      _ = S / ((l:ℝ) - 1) := by
          have hl0 : (l:ℝ) ≠ 0 := by positivity
          have hl1' : (l:ℝ) - 1 ≠ 0 := hlpos.ne'
          rw [pow_one, one_sub_div hl0, div_div_div_cancel_right₀ hl0, one_div, div_eq_mul_inv]
  have hlog : ((b - 1 : ℕ) : ℝ) ≤ Real.logb l ((m + S : ℕ) : ℝ) := by
    have e : b - 1 = Nat.log l (m + S) := by omega
    rw [e, Real.le_logb_iff_rpow_le hl1 (by exact_mod_cast (show 0 < m + S by omega)), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self l (show m + S ≠ 0 by omega)
  calc ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ)
      ≤ ((∑ i ∈ Ico 1 b, S / l ^ i + (b - 1) : ℕ) : ℝ) := by exact_mod_cast hN
    _ = ((∑ i ∈ Ico 1 b, S / l ^ i : ℕ) : ℝ) + ((b - 1 : ℕ) : ℝ) := by rw [Nat.cast_add]
    _ ≤ S / ((l:ℝ) - 1) + Real.logb l ((m + S : ℕ) : ℝ) := add_le_add hgeo hlog

theorem logb_natCast_nonneg (l : ℕ) (hl : (1 : ℝ) < l) (N : ℕ) : 0 ≤ Real.logb l (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · simp [h0]
  · exact Real.logb_nonneg hl (by exact_mod_cast h0)

theorem sum_padicValInt_Ico_le_div_sub_one_add_logb (l : ℕ) (hl2 : 2 ≤ l) (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ((∑ i ∈ Finset.Ico a (a + S), padicValInt l i : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + Real.logb l N := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hLN : 0 ≤ Real.logb l (N:ℝ) := logb_natCast_nonneg l hl1 N
  have hre : ∑ i ∈ Finset.Ico a (a + S), padicValInt l i = ∑ k ∈ range S, padicValInt l (a + (k:ℤ)) := by
    have himg : (range S).image (fun k : ℕ => a + (k:ℤ)) = Finset.Ico a (a + S) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨k, hk, rfl⟩
        omega
      · intro h
        exact ⟨(i - a).toNat, by omega, by omega⟩
    rw [← himg, Finset.sum_image]
    intro x _ y _ h
    simpa using h
  rw [hre]
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS
    simp [hLN]
  have hfirst := ha a (by simp only [Finset.mem_Ico]; omega)
  have hlast := ha (a + S - 1) (by simp only [Finset.mem_Ico]; omega)
  rw [abs_le] at hfirst hlast
  by_cases hpos : 0 < a
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = a - 1 := ⟨(a - 1).toNat, by omega⟩
    have hr : ∑ k ∈ range S, padicValInt l (a + (k:ℤ)) = ∑ k ∈ range S, padicValNat l (m + 1 + k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have e : a + (k:ℤ) = ((m + 1 + k : ℕ) : ℤ) := by push_cast; omega
      rw [show padicValInt l (a + (k:ℤ)) = padicValNat l (a + (k:ℤ)).natAbs from rfl, e, Int.natAbs_cast]
    rw [hr]
    refine (sum_padicVal_window_le l hl2 m S).trans (add_le_add le_rfl ?_)
    exact Real.logb_le_logb_of_le hl1 (by exact_mod_cast (show 0 < m + S by omega))
      (by exact_mod_cast (show m + S ≤ N by omega))
  · have hneg : a + S ≤ 0 := by
      by_contra hc
      have := ha 0 (by simp only [Finset.mem_Ico]; omega)
      exact this.1 rfl
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -a - S := ⟨(-a - S).toNat, by omega⟩
    have hr : ∑ k ∈ range S, padicValInt l (a + (k:ℤ)) = ∑ k ∈ range S, padicValNat l (m + 1 + k) := by
      refine (Finset.sum_range_reflect (fun k : ℕ => padicValInt l (a + (k:ℤ))) S).symm.trans ?_
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      have e : a + (((S - 1 - k : ℕ)) : ℤ) = -((m + 1 + k : ℕ) : ℤ) := by omega
      show padicValInt l (a + ((S - 1 - k : ℕ) : ℤ)) = _
      rw [e, show padicValInt l (-((m + 1 + k : ℕ) : ℤ)) = padicValNat l (-((m + 1 + k : ℕ) : ℤ)).natAbs from rfl,
        Int.natAbs_neg, Int.natAbs_cast]
    rw [hr]
    refine (sum_padicVal_window_le l hl2 m S).trans (add_le_add le_rfl ?_)
    exact Real.logb_le_logb_of_le hl1 (by exact_mod_cast (show 0 < m + S by omega))
      (by exact_mod_cast (show m + S ≤ N by omega))

private theorem sum_biUnion_le_sum_sum' {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset ℤ) (f : ℤ → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have h2 := Finset.sum_union_inter (s₁ := t j) (s₂ := s.biUnion t) (f := f)
    omega

theorem kappa_bound_window_sum (l : ℕ) (hl : 11 ≤ l) (ell S h : ℕ) (a : Fin ell → ℤ)
    (ha : ∀ k, ∀ i ∈ Finset.Ico (a k) (a k + S), i ≠ 0 ∧ |i| ≤ (h : ℤ))
    (JS : Finset ℤ) (hJS : JS ⊆ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S)) :
    (ell ≤ 3 → (((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) : ℕ) : ℝ)) ≤
      13 * S + 3 * Real.logb l (2 * (h : ℝ)) + 3) ∧
    (∀ R : ℕ, 1 ≤ R → ell ≤ R → (((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) : ℕ) : ℝ)) ≤
      3 * (R : ℝ) ^ 2 * (S + 1 + Real.logb l (2 * (h : ℝ)))) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hl11 : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hlm : (10:ℝ) ≤ (l:ℝ) - 1 := by linarith
  have hL0 : 0 ≤ Real.logb l (h:ℝ) := logb_natCast_nonneg l hl1 h
  have hL2 : Real.logb l (h:ℝ) ≤ Real.logb l (2 * (h:ℝ)) := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · simp [h0]
    · have : (0:ℝ) < h := by exact_mod_cast h0
      exact Real.logb_le_logb_of_le hl1 this (by linarith)
  have hsub : JS.erase 0 ⊆ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S) :=
    (Finset.erase_subset _ _).trans hJS
  have hC : (JS.erase 0).card ≤ ell * S := by
    calc (JS.erase 0).card ≤ (Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k, (Finset.Ico (a k) (a k + S)).card := Finset.card_biUnion_le
      _ = ell * S := by simp
  have h1 : ∑ i ∈ JS.erase 0, padicValInt l i ≤ ∑ k, ∑ i ∈ Finset.Ico (a k) (a k + S), padicValInt l i :=
    (Finset.sum_le_sum_of_subset hsub).trans (sum_biUnion_le_sum_sum' _ _ _)
  have hV : ((∑ i ∈ JS.erase 0, padicValInt l i : ℕ) : ℝ) ≤ ell * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) := by
    calc ((∑ i ∈ JS.erase 0, padicValInt l i : ℕ) : ℝ)
        ≤ ((∑ k, ∑ i ∈ Finset.Ico (a k) (a k + S), padicValInt l i : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ∑ k, ((∑ i ∈ Finset.Ico (a k) (a k + S), padicValInt l i : ℕ) : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ∑ _k : Fin ell, (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) :=
          Finset.sum_le_sum fun k _ => sum_padicValInt_Ico_le_div_sub_one_add_logb l (by omega) (a k) S h (ha k)
      _ = ell * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) := by simp [mul_add]
  have hQ : (((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i)) : ℕ) : ℝ) =
      ell + (ell + 1) * ((JS.erase 0).card : ℝ) + ((∑ i ∈ JS.erase 0, padicValInt l i : ℕ) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    push_cast
    ring
  have hCr : ((JS.erase 0).card : ℝ) ≤ ell * S := by exact_mod_cast hC
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hX0 : 0 ≤ S / ((l:ℝ) - 1) := by positivity
  have hX : S / ((l:ℝ) - 1) ≤ S / 10 := div_le_div_of_nonneg_left hS0 (by norm_num) hlm
  have he0 : (0:ℝ) ≤ ell := by positivity
  have hC0 : (0:ℝ) ≤ ((JS.erase 0).card : ℝ) := by positivity
  have g1 : ((ell:ℝ) + 1) * ((JS.erase 0).card : ℝ) ≤ ((ell:ℝ) + 1) * (ell * S) :=
    mul_le_mul_of_nonneg_left hCr (by positivity)
  rw [hQ]
  refine ⟨fun h3 => ?_, fun R hR hR' => ?_⟩
  · have he3 : (ell:ℝ) ≤ 3 := by exact_mod_cast h3
    have g2 : ((ell:ℝ) + 1) * (ell * S) ≤ 12 * S := by
      have : ((ell:ℝ) + 1) * ell ≤ 12 := by nlinarith
      nlinarith
    have g3 : (ell:ℝ) * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) ≤ 3 * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) :=
      mul_le_mul_of_nonneg_right he3 (by positivity)
    linarith
  · have hr1 : (1:ℝ) ≤ R := by exact_mod_cast hR
    have her : (ell:ℝ) ≤ R := by exact_mod_cast hR'
    have g2 : ((ell:ℝ) + 1) * (ell * S) ≤ 2 * (R:ℝ) ^ 2 * S := by
      have : ((ell:ℝ) + 1) * ell ≤ 2 * (R:ℝ) ^ 2 := by nlinarith
      nlinarith
    have her2 : (ell:ℝ) ≤ (R:ℝ) ^ 2 := by nlinarith
    have g3 : (ell:ℝ) * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) ≤ (R:ℝ) ^ 2 * (S + Real.logb l (2 * (h:ℝ))) :=
      mul_le_mul her2 (by linarith) (by positivity) (by positivity)
    have g4 : 0 ≤ (R:ℝ) ^ 2 * Real.logb l (2 * (h:ℝ)) := mul_nonneg (by positivity) (by linarith)
    nlinarith

theorem letter_size_add_le_height {n : ℕ} (b w S η : ℕ) (size : ZMod n → ℕ) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (x : ZMod n) :
    size x + S ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := by
  unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
  split_ifs with hT
  · by_cases hx : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size x
    · unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick at hx
      omega
    · have := hnt x hx
      omega
  · have hx : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size x := fun hh => hT ⟨x, hh⟩
    have := hnt x hx
    omega

theorem kappa_bound_of_length {n : ℕ} [NeZero n] (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (up : ZMod n → Bool)
    (size : ZMod n → ℕ) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (hsz : ∀ i, η < size i) (c : ZMod n) :
    ((arcOf b w S η up size).len c ≤ 3 → (kapC l (arcOf b w S η up size) c : ℝ) ≤
      13 * S + 3 * Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3) ∧
    (∀ R : ℕ, 1 ≤ R → (arcOf b w S η up size).len c ≤ R → (kapC l (arcOf b w S η up size) c : ℝ) ≤
      3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 + Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)))) := by
  let a : Fin ((arcOf b w S η up size).len c) → ℤ := fun k =>
    if up (c - ((k : ℕ) : ZMod n)) then -((size (c - ((k : ℕ) : ZMod n)) : ℕ) : ℤ) - S
    else ((size (c - ((k : ℕ) : ZMod n)) : ℕ) : ℤ)
  have hwin : ∀ k, ∀ i ∈ Finset.Ico (a k) (a k + S),
      i ≠ 0 ∧ |i| ≤ ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℤ) := by
    intro k i hi
    have h1 := letter_size_add_le_height b w S η size h20w hnt (c - ((k : ℕ) : ZMod n))
    have h2 := hsz (c - ((k : ℕ) : ZMod n))
    simp only [Finset.mem_Ico, a] at hi
    split_ifs at hi <;> exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩
  have hty : ∀ x, (arcOf b w S η up size).ty x =
      if up x then Formalism.MainNotions.LocalTheoryWindows.LT.up (size x) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size x) := fun _ => rfl
  have hSS : (arcOf b w S η up size).S = S := rfl
  have hJS : (arcOf b w S η up size).JS c ⊆ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S) := by
    intro i hi
    simp only [Formalism.MainNotions.ArcLiftingSetup.ArcP.JS, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rw [if_neg] at hi
      · simp at hi
      rintro ⟨s, -, hs⟩
      rw [hty] at hs
      split_ifs at hs
    · rw [Finset.mem_biUnion] at hi
      obtain ⟨s, hs, hi⟩ := hi
      rw [Finset.mem_range] at hs
      rw [Finset.mem_biUnion]
      refine ⟨⟨s, hs⟩, Finset.mem_univ _, ?_⟩
      rw [hty, hSS] at hi
      by_cases hu : up (c - (s : ZMod n)) <;> simp [a, hu] at hi ⊢ <;> omega
  exact kappa_bound_window_sum l hl ((arcOf b w S η up size).len c) S (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) a hwin
    ((arcOf b w S η up size).JS c) hJS

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem kappa_le_of_alternating : ∀ {n : ℕ} [NeZero n] (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (up : ZMod n → Bool)
    (size : ZMod n → ℕ) (h20 : 20 * S ≤ b) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (hAlt : Alt b η up size)
    (hsz : ∀ i, η < size i) (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts)
    (hlen : (arcOf b w S η up size).len c ≤ 3),
    (kapC l (arcOf b w S η up size) c : ℝ) ≤
      13 * S + 3 * Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 := by
  intro n _ l hl b w S η up size h20 h20w hnt hAlt hsz c hc hlen
  exact (kappa_bound_of_length l hl b w S η up size h20w hnt hsz c).1 hlen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem kappa_le_of_single_thick : ∀ {n : ℕ} [NeZero n] (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (up : ZMod n → Bool)
    (size : ZMod n → ℕ) (h20 : 20 * S ≤ b) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (R : ℕ) (hR : 1 ≤ R) (hOne : One b η R up size)
    (hsz : ∀ i, η < size i) (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts)
    (hlen : (arcOf b w S η up size).len c ≤ R),
    (kapC l (arcOf b w S η up size) c : ℝ) ≤
      3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 + Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) := by
  intro n _ l hl b w S η up size h20 h20w hnt R hR hOne hsz c hc hlen
  exact (kappa_bound_of_length l hl b w S η up size h20w hnt hsz c).2 R hR hlen

end Formalism.MainNotions.N.Ln17
