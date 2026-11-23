import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogbStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNatStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowCount

theorem v_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : ℤ) :
    0 ≤ v (z : C) := by
  have hn : ∀ n : ℕ, 0 ≤ v (n : C) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (le_min ih (by simp)) (v.map_add _ _)
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast hn n
  · push_cast; rw [v.map_neg]; exact hn n

theorem low_count_first_bound : FactorialWeightedSumBound := by
  intro C _ _ v M ρ g hg P B hB
  apply AddValuation.map_le_sum
  intro α hα
  rw [v.map_mul, v.map_mul]
  have h1 := hB α hα
  have h2 := hg α
  have h3 := v_intCast_nonneg v (P.coeff α)
  have h4 : (((B + ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) + (((0 - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ)
      ≤ v ((∏ m, (α m).factorial : ℕ) : C) + v (coeff α g) := add_le_add h1 h2
  rw [← WithTop.coe_add] at h4
  have h5 : (B + ∑ m, ρ m * α m) + (0 - ∑ m, ρ m * α m) = B := by ring
  rw [h5] at h4
  calc ((B : ℝ) : WithTop ℝ) = 0 + ((B : ℝ) : WithTop ℝ) := by simp
    _ ≤ _ := by rw [add_assoc]; exact add_le_add h3 h4

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem logb_two_le (p : ℕ) (hp : 3 ≤ p) : Real.logb p 2 ≤ 7 / 8 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have h3 : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp'
  have h : 8 * Real.log 2 ≤ 7 * Real.log 3 := by
    have := Real.log_le_log (by norm_num) (show (2:ℝ) ^ 8 ≤ 3 ^ 7 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  rw [Real.logb, div_le_iff₀ hlp]
  linarith

theorem low_count_third_bound : RadiusExponentInequality := by
  intro p i cr K ex hp hex hcr hK hK2
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith
  have hex' : (1 : ℝ) ≤ ex := by exact_mod_cast hex
  set D : ℝ := (p : ℝ) ^ 2 - 1 with hD
  have hD8 : 8 ≤ D := by nlinarith
  set q : ℝ := (p : ℝ) ^ (-(2 * (K : ℤ) + 1)) with hq
  have hq0 : 0 ≤ q := zpow_nonneg (by linarith) _
  have hqe : (ex : ℝ) * q ≤ 1 := by
    have hpos : (0 : ℝ) < (p : ℝ) ^ (2 * K + 1) := by positivity
    have : q = 1 / (p : ℝ) ^ (2 * K + 1) := by
      rw [hq, zpow_neg, one_div, show (2 * (K : ℤ) + 1) = ((2 * K + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    rw [this, mul_one_div, div_le_one hpos]
    exact_mod_cast hK
  have hrK : radius p K = (1 + q) / D := rfl
  have hrm : radius p (-1) = (1 + p) / D := by
    rw [hD]; simp only [radius]; norm_num
  have hpm : 1 / ((p : ℝ) - 1) = (1 + p) / D := by
    rw [hD, div_eq_div_iff (by linarith) (by nlinarith)]; ring
  have hL : Real.logb p (ex + 1) ≤ Real.logb p ex + 7 / 8 := by
    have h2 : ((ex : ℝ) + 1) ≤ ex * 2 := by linarith
    have := Real.logb_le_logb_of_le hp1 (by linarith) h2
    rw [Real.logb_mul (by linarith) (by norm_num)] at this
    linarith [logb_two_le p hp]
  have hi : (cr : ℝ) ≤ i := by exact_mod_cast hcr
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hii : (i : ℝ) ≤ (i : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ i := by exact_mod_cast h
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [hrK, hrm]
    have hdiv : (i : ℝ) * ex / ((p : ℝ) - 1) = i * ex * (1 / ((p : ℝ) - 1)) := by ring
    rw [hdiv, hpm]
    have key : ((i : ℝ) - cr) * ex * (ex * q) ≤ ((i : ℝ) - cr) * ex := by
      have := mul_le_mul_of_nonneg_left hqe (mul_nonneg (sub_nonneg.2 hi) (by positivity : (0:ℝ) ≤ ex))
      linarith
    have e : (i : ℝ) * ex * ((1 + p) / D) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) - i * ex * ((1 + q) / D)
        - ex * cr * ((1 + p) / D - (1 + q) / D)
        - ((((i : ℝ) - cr) * ex * p / D) - (i : ℝ) ^ 2 * (Real.logb p ex + 1))
        = (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) - ((i : ℝ) - cr) * (ex * q) / D := by
      field_simp; ring
    have h1 : ((i : ℝ) - cr) * (ex * q) / D ≤ i / 8 := by
      rw [div_le_iff₀ (by linarith)]
      have : ((i : ℝ) - cr) * (ex * q) ≤ (i : ℝ) - cr :=
        by nlinarith [mul_le_mul_of_nonneg_left hqe (sub_nonneg.2 hi)]
      nlinarith
    have h2 : (i : ℝ) ^ 2 / 8 ≤ (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) := by
      nlinarith [sq_nonneg (i : ℝ)]
    linarith
  · rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      have : 0 ≤ Real.logb p ex := Real.logb_nonneg hp1 hex'
      push_cast; linarith
    · rcases hK2 with h | h
      · omega
      · have h' : ((p : ℝ) ^ (2 * K - 1) : ℝ) ≤ ex := by exact_mod_cast h.le
        have := Real.logb_le_logb_of_le hp1 (by positivity) h'
        rw [Real.logb_pow, Real.logb_self_eq_one hp1] at this
        have hc : ((2 * K - 1 : ℕ) : ℝ) = 2 * (K : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc] at this
        linarith

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem rows_eq {i ex : ℕ} (α : Fin i × Fin i →₀ ℕ) (hdeg : Finsupp.degree α = i * ex)
    (hrow : ∀ e : Fin i, ∑ c : Fin i, α (e, c) ≤ ex) : ∀ e : Fin i, ∑ c : Fin i, α (e, c) = ex := by
  have hs : ∑ e : Fin i, ∑ c : Fin i, α (e, c) = ∑ e : Fin i, ex := by
    rw [← Fintype.sum_prod_type' (fun e c => α (e, c))]
    rw [Finsupp.degree_eq_sum] at hdeg
    simp [hdeg, mul_comm]
  intro e
  exact (Finset.sum_eq_sum_iff_of_le (fun e _ => hrow e)).1 hs e (Finset.mem_univ e)

theorem count_lt (i cr : ℕ) (hcr : cr ≤ i) (a b : ℝ) :
    ∑ e : Fin i, (if e.val < cr then a else b) = cr * a + (i - cr) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < cr then a else b) i, Finset.sum_ite]
  have h1 : (Finset.range i).filter (· < cr) = Finset.range cr := by
    ext k; simp; omega
  have h2 : ((Finset.range i).filter (fun k => ¬ k < cr)).card = i - cr := by
    have : (Finset.range i).filter (fun k => ¬ k < cr) = Finset.Ico cr i := by
      ext k; simp; omega
    rw [this, Nat.card_Ico]
  rw [Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  push_cast [hcr]; ring

theorem low_count_second_bound : FactorialMultiindexBound := by
  intro C _ _ v p hp hp3 hv i cr K ex hcr α hdeg hrow
  have hR := rows_eq α hdeg hrow
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, ?_⟩
  · apply le_of_eq
    rw [Fintype.sum_prod_type]
    have : ∀ e : Fin i, ∑ c : Fin i, (if (e, c).1.val < cr then radius p (-1) else radius p K) * (α (e, c) : ℝ)
        = (if e.val < cr then radius p (-1) else radius p K) * ex := by
      intro e
      rw [← hR e, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => this e), ← Finset.sum_mul, count_lt i cr hcr]
    ring
  · have hN : (∏ x, (α x).factorial : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
    rw [GlobalTheory.T.addValuation_natCast_eq_padicValNat' C v p hp hv _ hN]
    rw [WithTop.coe_le_coe]
    rw [GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp]
    have hle : ∀ x : Fin i × Fin i, α x ≤ ex := by
      intro x
      rw [← hR x.1]
      exact Finset.single_le_sum (f := fun c => α (x.1, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ x.2)
    have hterm : ∀ x : Fin i × Fin i, (α x : ℝ) / ((p : ℝ) - 1) - Real.logb p ((ex : ℝ) + 1)
        ≤ (padicValNat p (α x).factorial : ℝ) := by
      intro x
      rw [GlobalTheory.LegendreBounds.legendre_real p hp]
      have hd := GlobalTheory.T.digits_sum_le_mul_logb p (α x) hp
      have hlog : Real.logb p ((α x : ℝ) + 1) ≤ Real.logb p ((ex : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by have := hle x; push_cast; exact_mod_cast (by omega : α x + 1 ≤ ex + 1))
      have h0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [sub_div]
      have : (((Nat.digits p (α x)).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((ex : ℝ) + 1) := by
        rw [div_le_iff₀ h0]; nlinarith
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hterm x)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at hsum
    have htot : (∑ x : Fin i × Fin i, (α x : ℝ)) = i * ex := by
      rw [Finsupp.degree_eq_sum] at hdeg; exact_mod_cast hdeg
    rw [htot] at hsum
    push_cast at hsum ⊢
    nlinarith [hsum]

theorem lowC_all : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality :=
  ⟨low_count_first_bound, low_count_second_bound, low_count_third_bound⟩

end GlobalTheory.LowCount
