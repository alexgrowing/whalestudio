import Mathlib
import Formalism.PeriodIntegrals.SzEatI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.SizeDel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.BDivXNonneg
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.OrbitLabellings.TwoPowDvdSubOrAddOneOfOddAddOrderOfHP
import Development.AutomorphicArithmetic.OrbitLabellings.SumLogDivCubeLeOfTwoPowDvd

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

private lemma mul_log_div_cube_le_two (x k n : ℝ) (hx : 1 ≤ x) (hk : k ≤ x ^ 5) (hn : x ^ 2 ≤ n) :
    k * (Real.log n / n ^ 3) ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hn1 : 1 ≤ n := (one_le_pow₀ hx).trans hn
  set s := Real.sqrt n with hs
  have hss : n = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hxs : x ≤ s := Real.le_sqrt_of_sq_le hn
  have hs0 : 0 < s := by linarith
  have hl : Real.log n ≤ 2 * s := by
    rw [hss, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hs0
    push_cast
    linarith
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hk' : k ≤ s ^ 5 := hk.trans (pow_le_pow_left₀ hx0.le hxs 5)
  calc k * (Real.log n / n ^ 3) ≤ s ^ 5 * (2 * s / n ^ 3) := by gcongr
    _ = 2 := by rw [hss]; field_simp

private lemma rank_sizes_log_cube_bound {D : D7} (L : SizeData₂ D) (hSz : Formalism.MainNotions.SizesAt L) :
    1 ≤ D.R.e ∧ (D.R.k : ℝ) * (Real.log ((2 : ℝ) ^ D.R.e) / ((2 : ℝ) ^ D.R.e) ^ 3) ≤ 2 := by
  obtain ⟨hN, -, hK, -⟩ := hSz
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    refine hK.2.trans ?_
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
    unfold Formalism.MainNotions.szTh
    push_cast
    linarith
  have h1 : (D.R.n : ℝ) ≤ (D.R.o : ℝ) * (2 : ℝ) ^ D.R.e := by
    exact_mod_cast D.R.toFrame.ord_le_o_mul_two_pow
  have h2 : L.sc.x ^ (L.sc.eps / 100) * L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
    unfold Formalism.MainNotions.szTh
    push_cast
    linarith
  have h3 : (D.R.o : ℝ) * (2 : ℝ) ^ D.R.e ≤ L.sc.x ^ (L.sc.eps / 100) * (2 : ℝ) ^ D.R.e :=
    mul_le_mul_of_nonneg_right L.o_tie (by positivity)
  have hn : L.sc.x ^ 2 ≤ (2 : ℝ) ^ D.R.e :=
    le_of_mul_le_mul_left (h2.trans (h1.trans h3)) (Real.rpow_pos_of_pos hx0 _)
  refine ⟨?_, mul_log_div_cube_le_two _ _ _ hx1.le hk hn⟩
  rcases Nat.eq_zero_or_pos D.R.e with h | h
  · rw [h] at hn
    nlinarith
  · exact h

private lemma card_kind_le_rank (D : D7) (p : ℕ) : ((kindBC D p).card : ℝ) ≤ (D.R.f : ℝ) := by
  have : Fintype.card (Bool × HH D) = D.R.f := by
    simp [HH, Fintype.card_prod, D.R.card_A, Ranks.f, Ranks.n]
  rw [← this]
  exact_mod_cast Finset.card_le_univ _

private lemma eta_size_le_bound {D : D7} (L : SizeData₂ D) (hSz : Formalism.MainNotions.SizesAt L) : L.etaSz ≤ L.sc.b := by
  obtain ⟨-, -, -, -, hT, -, -, -, -, -, -, -, -, hEta, -⟩ := hSz
  have ht : (1 : ℝ) ≤ D.R.t := hT.1
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have : 1 ≤ D.R.k := by omega
    exact_mod_cast this
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := D.R.ord_pos
      omega
    exact_mod_cast this
  have hden : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf) (one_le_pow₀ hk)
  exact le_trans hEta.2.1 (div_le_self (PI.SzEatI.W.b_pos L).le hden)

private lemma log_prime_weighted_cost_bound (lp p k s c f N la b : ℝ) (hlp : 0 < lp) (hp : 0 < p) (hk : 0 ≤ k) (hs0 : 0 ≤ s)
    (hs : s ≤ f * (5 * b)) (hf : 0 ≤ f) (hla : 0 ≤ la) :
    lp * max 0 ((k - 1) * s / p ^ 3 + c * f * N ^ 2 * (la / lp)) ≤
      5 * f * b * (k * (lp / p ^ 3)) + |c| * f * (N ^ 2 * la) := by
  have h1 : (k - 1) * s ≤ k * (f * (5 * b)) := by nlinarith [mul_le_mul_of_nonneg_left hs hk]
  have h0 : 0 ≤ k * (f * (5 * b)) := mul_nonneg hk (hs0.trans hs)
  have h2 : (k - 1) * s / p ^ 3 ≤ k * (f * (5 * b)) / p ^ 3 := by gcongr
  have h3 : c * f * N ^ 2 * (la / lp) ≤ |c| * f * N ^ 2 * (la / lp) := by
    gcongr; exact le_abs_self c
  have h4 : max 0 ((k - 1) * s / p ^ 3 + c * f * N ^ 2 * (la / lp)) ≤
      k * (f * (5 * b)) / p ^ 3 + |c| * f * N ^ 2 * (la / lp) :=
    max_le (by positivity) (add_le_add h2 h3)
  refine (mul_le_mul_of_nonneg_left h4 hlp.le).trans (le_of_eq ?_)
  field_simp

theorem UpperTheory.sum_log_mul_max_zero_le_of_odd_addOrderOf :
    ∀ (ce : ErrC) (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ,
    ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), PI.SzEatI.Uni eps Ct CGam Cc CT2 PK D L P → x0 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    ∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p ∧ Odd (addOrderOf (hP D p)) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
    ∑ p ∈ S, Real.log p * max 0 (((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ^ 3 +
        ce.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) ≤
      C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n) := by
  intro ce eps Ct CGam Cc CT2 PK
  obtain ⟨x0, hx0⟩ := PI.SzEatI.W.stepA ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ eps
  refine ⟨10 + |ce.c6|, by positivity, x0, ?_⟩
  intro D L P hU hx hSz j hj S hS
  obtain ⟨hbb, -, hYR, hY1, hlog⟩ := hx0 D L hU.1 hx hSz
  simp only [PI.SzEatI.W.Rt, abs_zero, zero_mul, mul_zero, add_zero] at hYR
  set Y := L.sc.X'' D.R.n with hYdef
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hb1 := PI.SzEatI.W.one_le_b L
  have hη := eta_size_le_bound L hSz
  have ha1 : 1 ≤ L.sc.a := one_le_mul_of_one_le_of_one_le (PI.SzEatI.W.x_one_le L) hb1
  have hla : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := PI.SzEatI.W.n_one_le
  have hN1 : 1 ≤ Nm D := by
    have : 1 ≤ D.R.N D.R.m := by
      unfold Ranks.N; have := D.R.m_add_three_le_k; omega
    unfold Nm; exact_mod_cast this
  have hla8 : Real.log L.sc.a ≤ Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) := by
    refine Real.log_le_log (by linarith) (le_mul_of_one_le_left (by linarith) ?_)
    exact one_le_mul_of_one_le_of_one_le (by linarith) hN1
  have hYa : Y * (Nm D ^ 2 * Real.log L.sc.a) ≤ L.sc.b := by
    refine le_trans ?_ hYR
    have : 0 ≤ Y := by linarith
    gcongr
    linarith
  have hpt : ∀ p ∈ S, Real.log p * max 0 (((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ^ 3 +
        ce.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) ≤
      5 * (D.R.f : ℝ) * L.sc.b * ((D.R.k : ℝ) * (Real.log p / (p : ℝ) ^ 3)) +
        |ce.c6| * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log L.sc.a) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).1.one_lt
    have hw : ∀ z ∈ kindBC D p, 0 ≤ wPl D j z ∧ wPl D j z ≤ 5 * L.sc.b := fun z _ => by
      have := PI.SzEatI.W.stepW D L hSz hbb j hj z
      exact ⟨this.1, by linarith [this.2]⟩
    have hs0 : 0 ≤ ∑ z ∈ kindBC D p, wPl D j z := Finset.sum_nonneg fun z hz => (hw z hz).1
    have hs : ∑ z ∈ kindBC D p, wPl D j z ≤ (D.R.f : ℝ) * (5 * L.sc.b) := by
      calc ∑ z ∈ kindBC D p, wPl D j z ≤ ∑ _z ∈ kindBC D p, 5 * L.sc.b :=
            Finset.sum_le_sum fun z hz => (hw z hz).2
        _ = ((kindBC D p).card : ℝ) * (5 * L.sc.b) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * (5 * L.sc.b) :=
            mul_le_mul_of_nonneg_right (card_kind_le_rank D p) (by linarith)
    exact log_prime_weighted_cost_bound _ _ _ _ _ _ _ _ _ (Real.log_pos hp1) (by linarith) hk hs0 hs hf hla
  obtain ⟨he, hke⟩ := rank_sizes_log_cube_bound L hSz
  have hM := UpperTheory.sum_log_div_cube_le_of_two_pow_dvd D.R.e he S
    (fun p hp => (UpperTheory.two_pow_dvd_sub_or_add_one_of_odd_addOrderOf_hP D p (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2.1).1)
  have hM2 : (D.R.k : ℝ) * ∑ p ∈ S, Real.log p / (p : ℝ) ^ 3 ≤ 2 :=
    (mul_le_mul_of_nonneg_left hM hk).trans hke
  have hcard : (S.card : ℝ) ≤ Y :=
    PI.SzEatI.W.card_le_of_le S Y (by linarith) (fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2.2⟩)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hcf : 0 ≤ |ce.c6| * (D.R.f : ℝ) := by positivity
  calc 5 * (D.R.f : ℝ) * L.sc.b * ((D.R.k : ℝ) * ∑ p ∈ S, Real.log p / (p : ℝ) ^ 3) +
        (S.card : ℝ) * (|ce.c6| * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log L.sc.a))
      ≤ 5 * (D.R.f : ℝ) * L.sc.b * 2 + Y * (|ce.c6| * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log L.sc.a)) := by
        gcongr
    _ = 10 * (D.R.f : ℝ) * L.sc.b + |ce.c6| * (D.R.f : ℝ) * (Y * (Nm D ^ 2 * Real.log L.sc.a)) := by ring
    _ ≤ 10 * (D.R.f : ℝ) * L.sc.b + |ce.c6| * (D.R.f : ℝ) * L.sc.b := by gcongr
    _ = (10 + |ce.c6|) * (D.R.f : ℝ) * L.sc.b * 1 := by ring
    _ ≤ (10 + |ce.c6|) * (D.R.f : ℝ) * L.sc.b * Real.log Y := by gcongr
