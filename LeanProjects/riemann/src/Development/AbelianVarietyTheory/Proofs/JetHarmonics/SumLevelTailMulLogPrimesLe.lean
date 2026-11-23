import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.TailPrimeSum

theorem thBounds : ThBounds := by
  intro k l hk hl
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨-, h3, hlt, he⟩ := GlobalTheory.LevelsOrbits.thlEq k l hk hl
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [he]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) h3)
  · rw [he]
    exact inv_strictAnti₀ (by positivity) hlt
  · have h1 : (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ 3 := by
      calc (k : ℝ) ^ ((3 : ℝ) / 2) < ((l : ℝ) ^ 2) ^ ((3 : ℝ) / 2) :=
            Real.rpow_lt_rpow (by positivity) h (by norm_num)
        _ = (l : ℝ) ^ 3 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
            norm_num
    have h2 : i0 k l ≤ 3 := Nat.sInf_le ⟨⟨1, by norm_num⟩, le_rfl, h1⟩
    rw [he, le_antisymm h2 h3]

lemma sum_log_le (Q : Finset ℕ) (x : ℝ) (hx : 0 ≤ x) (hQ : ∀ p ∈ Q, p.Prime)
    (hle : ∀ p ∈ Q, (p : ℝ) ≤ x) : ∑ p ∈ Q, Real.log p ≤ 3 / 2 * x := by
  have h1 : ∑ p ∈ Q, Real.log p ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
      (fun p _ _ => Real.log_natCast_nonneg p)
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨(hQ p hp).pos, Nat.le_floor (hle p hp)⟩, hQ p hp⟩
  have h2 := Chebyshev.theta_le_log4_mul_x hx
  have h3 : Real.log 4 ≤ 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have := mul_le_mul_of_nonneg_right h3 hx
  linarith

lemma tail_le (N : ℕ) : ∀ (Q : Finset ℕ) (Y : ℝ), 0 < Y → (∀ p ∈ Q, p.Prime) →
    (∀ p ∈ Q, Y < p ∧ (p : ℝ) ≤ 2 ^ N * Y) →
    ∑ p ∈ Q, ((p : ℝ) ^ 3)⁻¹ * Real.log p ≤ 4 / Y ^ 2 := by
  induction N with
  | zero =>
    intro Q Y hY _ h
    have : Q = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      have := h p hp
      simp only [pow_zero, one_mul] at this
      linarith [this.1, this.2]
    rw [this, Finset.sum_empty]
    positivity
  | succ N ih =>
    intro Q Y hY hQ h
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) ≤ 2 * Y)]
    have h1 : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ 2 * Y), ((p : ℝ) ^ 3)⁻¹ * Real.log p
        ≤ (Y ^ 3)⁻¹ * (3 / 2 * (2 * Y)) := by
      calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ 2 * Y), (Y ^ 3)⁻¹ * Real.log p := by
            refine Finset.sum_le_sum fun p hp => ?_
            have := (h p (Finset.mem_filter.1 hp).1).1
            refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
            exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hY.le this.le 3)
        _ ≤ _ := by
            rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_log_le _ _ (by positivity) (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
              (fun p hp => (Finset.mem_filter.1 hp).2)
    have h2 := ih (Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ 2 * Y)) (2 * Y) (by positivity)
      (fun p hp => hQ p (Finset.mem_filter.1 hp).1) (fun p hp => by
        obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
        refine ⟨not_le.1 b, ?_⟩
        have := (h p a).2
        rw [pow_succ, mul_assoc] at this
        exact this)
    have h3 : (Y ^ 3)⁻¹ * (3 / 2 * (2 * Y)) + 4 / (2 * Y) ^ 2 = 4 / Y ^ 2 := by
      field_simp
      ring
    linarith

theorem main : Formalism.UnitaryBoundIntegral.ThBounds ∧ ∀ (k : ℕ) (Q : Finset ℕ), 1 ≤ k → (∀ p ∈ Q, p.Prime) →
    ∑ p ∈ Q, thl k p * Real.log p ≤ 20 / k := by
  refine ⟨thBounds, fun k Q hk hQ => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set Y : ℝ := Real.sqrt k with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_sqrt.2 hk'
  have hY : 0 < Y := by linarith
  have hY2 : Y ^ 2 = k := Real.sq_sqrt (by positivity)
  have hY3 : (k : ℝ) ^ ((3 : ℝ) / 2) = Y ^ 3 := by
    rw [← hY2, ← Real.rpow_natCast, ← Real.rpow_mul hY.le, ← Real.rpow_natCast]
    norm_num
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) ≤ Y)]
  have h1 : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ Y), thl k p * Real.log p
      ≤ (Y ^ 3)⁻¹ * (3 / 2 * Y) := by
    calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ Y), (Y ^ 3)⁻¹ * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          rw [← hY3]
          exact (thBounds k p hk (hQ p (Finset.mem_filter.1 hp).1).two_le).2.1.le
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_log_le _ _ hY.le (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
            (fun p hp => (Finset.mem_filter.1 hp).2)
  have h2 : ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), thl k p * Real.log p ≤ 4 / Y ^ 2 := by
    calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), ((p : ℝ) ^ 3)⁻¹ * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          exact (thBounds k p hk (hQ p (Finset.mem_filter.1 hp).1).two_le).1
      _ ≤ _ := by
          refine tail_le (Q.sup id) _ Y hY (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
            (fun p hp => ?_)
          obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
          refine ⟨not_le.1 b, ?_⟩
          have h3 : p ≤ Q.sup id := Finset.le_sup (f := id) a
          have h4 : p ≤ 2 ^ (Q.sup id) := h3.trans Nat.lt_two_pow_self.le
          have h5 : (p : ℝ) ≤ 2 ^ (Q.sup id) := by exact_mod_cast h4
          exact h5.trans (le_mul_of_one_le_right (by positivity) hY1)
  have h3 : (Y ^ 3)⁻¹ * (3 / 2 * Y) + 4 / Y ^ 2 = (11 / 2) / Y ^ 2 := by
    field_simp
    ring
  have h4 : (11 / 2 : ℝ) / Y ^ 2 ≤ 20 / k := by
    rw [hY2]
    gcongr
    norm_num
  linarith

end GlobalTheory.TailPrimeSum
