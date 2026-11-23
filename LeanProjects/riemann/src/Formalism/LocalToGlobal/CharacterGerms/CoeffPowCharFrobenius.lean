import Formalism.LocalToGlobal.CharacterGerms.FrobSerSt

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open ValuationNonnegativity

namespace FrobP

variable {C : Type} [Field C] {V : VF C}

theorem ge_intCast (z : ℤ) : V.Ge 0 (z : C) := by
  have hnat : ∀ m : ℕ, (0 : WithTop ℝ) ≤ V.v (m : C) := by
    intro m
    induction m with
    | zero => simp [AddValuation.map_zero]
    | succ k ih =>
      push_cast
      exact le_trans (le_min ih (by rw [AddValuation.map_one])) (AddValuation.map_add _ _ _)
  unfold VF.Ge
  rw [WithTop.coe_zero]
  rcases Int.eq_nat_or_neg z with ⟨m, rfl | rfl⟩
  · simpa using hnat m
  · push_cast
    rw [AddValuation.map_neg]
    simpa using hnat m

theorem not_mm_nat {m : ℕ} (hm : ¬ V.l ∣ m) : ¬ V.MM (m : C) := by
  intro h
  have hcop : Nat.Coprime V.l m := (Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hm
  have hA := ge_intCast (V := V) (Nat.gcdA V.l m)
  have hB := ge_intCast (V := V) (Nat.gcdB V.l m)
  unfold VF.Ge at hA hB
  rw [WithTop.coe_zero] at hA hB
  unfold VF.MM at h
  have h0 := Nat.gcd_eq_gcd_ab V.l m
  rw [Nat.Coprime.gcd_eq_one hcop] at h0
  have hsum := congrArg (fun z : ℤ => (z : C)) h0
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_one, Int.cast_one] at hsum
  have h1 : (0 : WithTop ℝ) < V.v ((V.l : C) * ((Nat.gcdA V.l m : ℤ) : C)) := by
    rw [AddValuation.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hA)
  have h2 : (0 : WithTop ℝ) < V.v ((m : C) * ((Nat.gcdB V.l m : ℤ) : C)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le h (le_add_of_nonneg_right hB)
  have hmin := AddValuation.map_add V.v ((V.l : C) * ((Nat.gcdA V.l m : ℤ) : C)) ((m : C) * ((Nat.gcdB V.l m : ℤ) : C))
  rw [← hsum, AddValuation.map_one] at hmin
  exact absurd hmin (not_le.mpr (lt_min h1 h2))

theorem mm_of_mul_nat {c : C} {m : ℕ} (hm : ¬ V.l ∣ m) (h : V.MM (c * m)) : V.MM c := by
  have hge := ge_intCast (V := V) (m : ℤ)
  unfold VF.Ge at hge
  rw [WithTop.coe_zero, Int.cast_natCast] at hge
  have h0 : V.v (m : C) = 0 := le_antisymm (not_lt.mp (not_mm_nat hm)) hge
  unfold VF.MM at h ⊢
  rwa [AddValuation.map_mul, h0, add_zero] at h

end FrobP

open FrobP in
theorem frobSer : FrobSerSt := by
  intro C _ V σ f hf μ ⟨i, hi⟩
  have hpos : 1 ≤ μ i := by
    rcases Nat.eq_zero_or_pos (μ i) with h0 | h0
    · rw [h0] at hi
      exact absurd (dvd_zero _) hi
    · exact h0
  have h1 := hf i (μ - Finsupp.single i 1)
  rw [MvPowerSeries.coeff_pderiv] at h1
  have e1 : μ - Finsupp.single i 1 + Finsupp.single i 1 = μ :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hpos)
  have e2 : (μ - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = μ i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  rw [e1] at h1
  have e3 : (((μ - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : C) + 1 = ((μ i : ℕ) : C) := by
    rw [← e2]
    push_cast
    ring
  rw [e3] at h1
  exact FrobP.mm_of_mul_nat hi h1

namespace FrobP

variable {C : Type} [Field C] {V : VF C}

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one

theorem valuation_coeff_mul_nonneg {f g : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f))
    (hg : ∀ n, V.Ge 0 (PowerSeries.coeff n g)) : ∀ n, V.Ge 0 (PowerSeries.coeff n (f * g)) := by
  intro n
  unfold VF.Ge at *
  rw [PowerSeries.coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  have h1 := hf x.1
  have h2 := hg x.2
  rw [WithTop.coe_zero] at h1 h2 ⊢
  exact add_nonneg h1 h2

theorem valuation_coeff_pow_nonneg {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) (k : ℕ) :
    ∀ n, V.Ge 0 (PowerSeries.coeff n (f ^ k)) := by
  induction k with
  | zero =>
    intro n
    unfold VF.Ge
    rw [pow_zero, PowerSeries.coeff_one, WithTop.coe_zero]
    split_ifs
    · rw [AddValuation.map_one]
    · rw [AddValuation.map_zero]
      exact le_top
  | succ k ih =>
    rw [pow_succ]
    exact valuation_coeff_mul_nonneg ih hf

theorem frob_ser {A B : PowerSeries C} (hA : ∀ n, V.Ge 0 (PowerSeries.coeff n A))
    (hB : ∀ n, V.Ge 0 (PowerSeries.coeff n B)) (m : ℕ) :
    V.MM (PowerSeries.coeff m ((A + B) ^ V.l - A ^ V.l - B ^ V.l)) := by
  obtain ⟨l', hl'⟩ : ∃ l', V.l = l' + 1 := ⟨V.l - 1, (Nat.succ_pred_eq_of_pos V.l_prime.pos).symm⟩
  have hmid : (A + B) ^ V.l - A ^ V.l - B ^ V.l =
      ∑ i ∈ Finset.range l', ((V.l.choose (i + 1) : ℕ) : C) • (A ^ (i + 1) * B ^ (V.l - (i + 1))) := by
    rw [add_pow, hl', Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero, Nat.sub_self,
      Nat.sub_zero, one_mul]
    have hsm : ∀ i ∈ Finset.range l', A ^ (i + 1) * B ^ (l' + 1 - (i + 1)) *
        (((l' + 1).choose (i + 1) : ℕ) : PowerSeries C) =
        (((l' + 1).choose (i + 1) : ℕ) : C) • (A ^ (i + 1) * B ^ (l' + 1 - (i + 1))) := fun i _ => by
      rw [mul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hsm]
    ring
  rw [hmid, map_sum]
  unfold VF.MM
  refine lt_of_lt_of_le zero_lt_one (AddValuation.map_le_sum _ fun i hi => ?_)
  rw [LinearMap.map_smul, smul_eq_mul, AddValuation.map_mul]
  have hi' := Finset.mem_range.mp hi
  obtain ⟨q, hq⟩ := V.l_prime.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hq' : (((V.l.choose (i + 1)) : ℕ) : C) = (V.l : C) * ((q : ℤ) : C) := by
    rw [hq]
    push_cast
    ring
  rw [hq', AddValuation.map_mul, V.v_l]
  have hqge := ge_intCast (V := V) (q : ℤ)
  have hcoef := valuation_coeff_mul_nonneg (valuation_coeff_pow_nonneg hA (i + 1)) (valuation_coeff_pow_nonneg hB (V.l - (i + 1))) m
  unfold VF.Ge at hqge hcoef
  rw [WithTop.coe_zero] at hqge hcoef
  calc (1 : WithTop ℝ) = 1 + 0 + 0 := by simp
    _ ≤ 1 + V.v ((q : ℤ) : C) + V.v (PowerSeries.coeff m (A ^ (i + 1) * B ^ (V.l - (i + 1)))) :=
      add_le_add (add_le_add le_rfl hqge) hcoef

theorem coeff_pow_char_frobenius : ∀ (m : ℕ) (f : PowerSeries C), (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
    V.MM (PowerSeries.coeff m (f ^ V.l) - if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) := by
  have hl := V.l_prime
  have hl0 : 0 < V.l := hl.pos
  have mm_add : ∀ x y : C, V.MM x → V.MM y → V.MM (x + y) := fun x y hx hy => by
    unfold VF.MM at *
    exact lt_of_lt_of_le (lt_min hx hy) (AddValuation.map_add _ _ _)
  have mm_zero : V.MM (0 : C) := by
    unfold VF.MM
    rw [AddValuation.map_zero]
    exact WithTop.coe_lt_top 0
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro f hf
  set a := PowerSeries.constantCoeff f with ha
  set g := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f with hgdef
  have hfg : f = PowerSeries.C a + PowerSeries.X * g := by
    ext n
    cases n with
    | zero => simp [a, g]
    | succ k => simp [g, PowerSeries.coeff_succ_X_mul]
  have hCa : ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.C a)) := by
    intro n
    rw [PowerSeries.coeff_C]
    split_ifs
    · have := hf 0
      simpa [a] using this
    · unfold VF.Ge
      rw [AddValuation.map_zero]
      exact le_top
  have hg : ∀ n, V.Ge 0 (PowerSeries.coeff n g) := fun n => by simpa [g] using hf (n + 1)
  have hXg : ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.X * g)) := by
    intro n
    cases n with
    | zero =>
      unfold VF.Ge
      simp [AddValuation.map_zero]
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      exact hg k
  have hfr := frob_ser hCa hXg m
  rw [← hfg, map_sub, map_sub] at hfr
  have e1 : PowerSeries.coeff m (PowerSeries.C a ^ V.l) = if m = 0 then a ^ V.l else 0 := by
    rw [← map_pow, PowerSeries.coeff_C]
  have e2 : PowerSeries.coeff m ((PowerSeries.X * g) ^ V.l) =
      if V.l ≤ m then PowerSeries.coeff (m - V.l) (g ^ V.l) else 0 := by
    rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  have hsec : V.MM (PowerSeries.coeff m (PowerSeries.C a ^ V.l) + PowerSeries.coeff m ((PowerSeries.X * g) ^ V.l) -
      if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) := by
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have hnl : ¬ V.l ≤ 0 := by omega
      simp only [if_true, hnl, if_false, add_zero, dvd_zero, Nat.zero_div]
      rw [show PowerSeries.coeff 0 f = a by simp [a], sub_self]
      exact mm_zero
    · by_cases hlm : V.l ≤ m
      · have hm0 : m ≠ 0 := by omega
        have hdiv : (V.l ∣ m) ↔ (V.l ∣ m - V.l) := by
          constructor
          · intro h; exact Nat.dvd_sub h (dvd_refl _)
          · intro h
            have := Nat.dvd_add h (dvd_refl V.l)
            rwa [Nat.sub_add_cancel hlm] at this
        have hq : m / V.l = (m - V.l) / V.l + 1 := Nat.div_eq_sub_div hl0 hlm
        have hih := ih (m - V.l) (by omega) g hg
        simp only [hm0, if_false, hlm, if_true, zero_add]
        have e3 : (if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) =
            if V.l ∣ m - V.l then PowerSeries.coeff ((m - V.l) / V.l) g ^ V.l else 0 := by
          by_cases h : V.l ∣ m
          · rw [if_pos h, if_pos (hdiv.1 h), hq]
            simp [g]
          · rw [if_neg h, if_neg (fun h' => h (hdiv.2 h'))]
        rw [e3]
        exact hih
      · have hm0 : m ≠ 0 := by omega
        have hnd : ¬ V.l ∣ m := fun h => hlm (Nat.le_of_dvd hpos h)
        simp only [hm0, if_false, hlm, hnd, add_zero, sub_self]
        exact mm_zero
  have h := mm_add _ _ hfr hsec
  convert h using 1
  ring

end FrobP

open FrobP in
theorem frobPow : FrobPowSt := by
  intro C _ V f hf
  refine ⟨fun n => ?_, fun m hm => ?_⟩
  · have h := FrobP.coeff_pow_char_frobenius (V := V) (V.l * n) f hf
    rwa [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ V.l_prime.pos] at h
  · have h := FrobP.coeff_pow_char_frobenius (V := V) m f hf
    rwa [if_neg hm, sub_zero] at h

end Formalism.L2.FormalSeriesBounds
