import Mathlib

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Finset

theorem padicValNat_factorial_add_sum (l : ℕ) [Fact l.Prime] (m S : ℕ) :
    padicValNat l m.factorial + ∑ j ∈ range S, padicValNat l (m + 1 + j) =
      padicValNat l (m + S).factorial := by
  induction S with
  | zero => simp
  | succ n ih =>
    have h1 : (m + (n + 1)).factorial = (m + n + 1) * (m + n).factorial := by
      rw [show m + (n + 1) = m + n + 1 by omega, Nat.factorial_succ]
    have h2 : padicValNat l ((m + n + 1) * (m + n).factorial) =
        padicValNat l (m + n + 1) + padicValNat l (m + n).factorial :=
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _)
    rw [Finset.sum_range_succ, h1, h2, show m + 1 + n = m + n + 1 by omega]
    omega

theorem padicValNat_factorial_le_div_sub_one' (l : ℕ) [hp : Fact l.Prime] (n : ℕ) :
    (padicValNat l n.factorial : ℝ) ≤ n / ((l : ℝ) - 1) := by
  have hl : 2 ≤ l := hp.out.two_le
  have hlR : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have key := sub_one_mul_padicValNat_factorial (p := l) n
  have hle : (l - 1) * padicValNat l n.factorial ≤ n := by
    rw [key]; exact Nat.sub_le _ _
  have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h' : ((l : ℝ) - 1) * (padicValNat l n.factorial : ℝ) ≤ n := by
    rw [← hcast]; exact_mod_cast hle
  rw [le_div_iff₀ hlR]
  linarith [mul_comm ((l : ℝ) - 1) (padicValNat l n.factorial : ℝ)]

private theorem floor_div_add_sub_floor_div_le_div_add_one (q m S : ℕ) (hq : 0 < q) :
    (((m + S) / q : ℕ) : ℝ) - ((m / q : ℕ) : ℝ) ≤ (S : ℝ) / (q : ℝ) + 1 := by
  have h1 : (m + S) / q * q ≤ m + S := Nat.div_mul_le_self _ _
  have h2 : m < q * (m / q) + q := by
    have h3 := Nat.div_add_mod m q
    have h4 := Nat.mod_lt m hq
    omega
  have h1' : (((m + S) / q : ℕ) : ℝ) * q ≤ (m : ℝ) + S := by exact_mod_cast h1
  have h2' : (m : ℝ) < q * ((m / q : ℕ) : ℝ) + q := by exact_mod_cast h2
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h5 : ((((m + S) / q : ℕ) : ℝ) - ((m / q : ℕ) : ℝ) - 1) * q ≤ S := by
    nlinarith
  have h6 : (((m + S) / q : ℕ) : ℝ) - ((m / q : ℕ) : ℝ) - 1 ≤ S / q := by
    rw [le_div_iff₀ hq']; exact h5
  linarith

private theorem sum_padicValNat_window_le_of_log_lt (l : ℕ) [hp : Fact l.Prime] (m S b : ℕ)
    (hb : Nat.log l (m + S) < b) :
    ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + ((b - 1 : ℕ) : ℝ) := by
  have hl : 2 ≤ l := hp.out.two_le
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hA := padicValNat_factorial (p := l) (n := m + S) hb
  have hB := padicValNat_factorial (p := l) (n := m)
    (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)
  have h1 := padicValNat_factorial_add_sum l m S
  rw [hA, hB] at h1
  have h1' : ∑ i ∈ Finset.Ico 1 b, ((m / l ^ i : ℕ) : ℝ) +
      ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) =
      ∑ i ∈ Finset.Ico 1 b, (((m + S) / l ^ i : ℕ) : ℝ) := by
    exact_mod_cast h1
  have key : ∀ i ∈ Finset.Ico 1 b, (((m + S) / l ^ i : ℕ) : ℝ) - ((m / l ^ i : ℕ) : ℝ) ≤
      (S : ℝ) * ((l : ℝ)⁻¹) ^ i + 1 := by
    intro i _
    have hq : 0 < l ^ i := pow_pos (by omega) i
    have := floor_div_add_sub_floor_div_le_div_add_one (l ^ i) m S hq
    rw [Nat.cast_pow] at this
    rw [inv_pow, ← div_eq_mul_inv]
    exact this
  have hsum : ∑ i ∈ Finset.Ico 1 b, (((m + S) / l ^ i : ℕ) : ℝ) -
      ∑ i ∈ Finset.Ico 1 b, ((m / l ^ i : ℕ) : ℝ) ≤
      ∑ i ∈ Finset.Ico 1 b, ((S : ℝ) * ((l : ℝ)⁻¹) ^ i + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum key
  have hl0 : (l : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hl1 : (l : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hgeom : ∑ i ∈ Finset.Ico 1 b, ((l : ℝ)⁻¹) ^ i ≤ 1 / ((l : ℝ) - 1) := by
    have hx0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
    have hx1 : (l : ℝ)⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_one (by linarith)]; linarith
    refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans (le_of_eq ?_)
    rw [pow_one]
    field_simp
  have hcard : ∑ i ∈ Finset.Ico 1 b, ((S : ℝ) * ((l : ℝ)⁻¹) ^ i + 1) =
      S * ∑ i ∈ Finset.Ico 1 b, ((l : ℝ)⁻¹) ^ i + ((b - 1 : ℕ) : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_one]
  have hS : (S : ℝ) * ∑ i ∈ Finset.Ico 1 b, ((l : ℝ)⁻¹) ^ i ≤ S / ((l : ℝ) - 1) := by
    calc (S : ℝ) * ∑ i ∈ Finset.Ico 1 b, ((l : ℝ)⁻¹) ^ i ≤ S * (1 / ((l : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = S / ((l : ℝ) - 1) := by rw [mul_one_div]
  linarith

private theorem natLog_le_logb_natCast_of_two_le (l n : ℕ) (hl : 2 ≤ l) :
    ((Nat.log l n : ℕ) : ℝ) ≤ Real.logb l (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hl1 : (1 : ℝ) < l := by
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    rw [Real.le_logb_iff_rpow_le hl1 (by exact_mod_cast hn), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self l hn.ne'

theorem sum_padicValNat_window_le (l : ℕ) [hp : Fact l.Prime] (m S : ℕ) :
    ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + Real.logb l ((m + S : ℕ) : ℝ) := by
  have hl : 2 ≤ l := hp.out.two_le
  have h := sum_padicValNat_window_le_of_log_lt l m S (Nat.log l (m + S) + 1) (Nat.lt_succ_self _)
  have h2 := natLog_le_logb_natCast_of_two_le l (m + S) hl
  simp only [Nat.add_sub_cancel] at h
  linarith

private theorem sum_Ico_int_eq_sum_range_add (a : ℤ) (S : ℕ) (f : ℤ → ℕ) :
    ∑ i ∈ Finset.Ico a (a + S), f i = ∑ j ∈ range S, f (a + j) := by
  induction S with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Ico a (a + ((n + 1 : ℕ) : ℤ)) = insert (a + n) (Finset.Ico a (a + n)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Ico]
      push_cast
      constructor <;> intro h <;> omega
    rw [hI, Finset.sum_insert (by simp), ih, Finset.sum_range_succ, add_comm]

theorem exists_sum_padicValInt_window_eq (l : ℕ) (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ∃ m : ℕ, m + S ≤ N ∧ ∑ i ∈ Finset.Ico a (a + S), padicValInt l i =
      ∑ j ∈ range S, padicValNat l (m + 1 + j) := by
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · exact ⟨0, by simp, by simp⟩
  have hfirst := ha a (by simp only [Finset.mem_Ico]; omega)
  have hlast := ha (a + S - 1) (by simp only [Finset.mem_Ico]; omega)
  rw [sum_Ico_int_eq_sum_range_add]
  rcases lt_or_gt_of_ne hfirst.1 with hneg | hpos
  · have hend : a + S ≤ 0 := by
      by_contra hc
      have h0 := ha 0 (by simp only [Finset.mem_Ico]; omega)
      exact h0.1 rfl
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -a - S by omega)
    refine ⟨m, ?_, ?_⟩
    · have := (abs_le.mp hfirst.2).1
      omega
    · rw [← Finset.sum_range_reflect (fun j => padicValNat l (m + 1 + j)) S]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have he : a + (j : ℤ) = -(((m + 1 + (S - 1 - j) : ℕ)) : ℤ) := by omega
      rw [padicValInt, he, Int.natAbs_neg]
      rfl
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ a - 1 by omega)
    refine ⟨m, ?_, ?_⟩
    · have := (abs_le.mp hlast.2).2
      omega
    · apply Finset.sum_congr rfl
      intro j _
      have he : a + (j : ℤ) = ((m + 1 + j : ℕ) : ℤ) := by push_cast; omega
      rw [padicValInt, he]
      rfl

theorem sum_padicValInt_window_le (l : ℕ) [Fact l.Prime] (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ((∑ i ∈ Finset.Ico a (a + S), padicValInt l i : ℕ) : ℝ) ≤ N / ((l : ℝ) - 1) := by
  obtain ⟨m, hmN, heq⟩ := exists_sum_padicValInt_window_eq l a S N ha
  rw [heq]
  have h1 := padicValNat_factorial_add_sum l m S
  have h2 := padicValNat_factorial_le_div_sub_one' l (m + S)
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlR : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h3n : ∑ j ∈ range S, padicValNat l (m + 1 + j) ≤ padicValNat l (m + S).factorial := by
    omega
  have h3 : ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      (padicValNat l (m + S).factorial : ℝ) := by exact_mod_cast h3n
  have h4 : ((m + S : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ N / ((l : ℝ) - 1) := by
    rw [le_div_iff₀ hlR, div_mul_cancel₀ _ hlR.ne']
    exact_mod_cast hmN
  linarith

theorem sum_padicValInt_window_le_logb (l : ℕ) [Fact l.Prime] (a : ℤ) (S N : ℕ) (hN : 1 ≤ N)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ((∑ i ∈ Finset.Ico a (a + S), padicValInt l i : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + Real.logb l N := by
  obtain ⟨m, hmN, heq⟩ := exists_sum_padicValInt_window_eq l a S N ha
  rw [heq]
  have h1 := sum_padicValNat_window_le l m S
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h2 : Real.logb l ((m + S : ℕ) : ℝ) ≤ Real.logb l N := by
    rcases Nat.eq_zero_or_pos (m + S) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg hl1 (by exact_mod_cast hN)
    · exact Real.logb_le_logb_of_le hl1 (by exact_mod_cast hpos) (by exact_mod_cast hmN)
  linarith

theorem sum_biUnion_le_sum_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℤ)
    (f : ℤ → ℕ) : ∑ i ∈ s.biUnion t, f i ≤ ∑ k ∈ s, ∑ i ∈ t k, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hk]
    have h : ∑ x ∈ t k ∪ s.biUnion t, f x + ∑ x ∈ t k ∩ s.biUnion t, f x =
        ∑ x ∈ t k, f x + ∑ x ∈ s.biUnion t, f x := Finset.sum_union_inter
    omega

end Formalism.MainNotions.N.FrobeniusPowerSeries
