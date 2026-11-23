import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.PrimeWeightedRemainderBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
import Development.AutomorphicArithmetic.OrbitLabellings.SumLogMulMaxZeroLeOfOddAddOrderOf

noncomputable section

namespace UpperTheory.G2

open Formalism.BasicNotions Formalism.MainNotions.G PI.SzEatI.W

theorem szEatI_of_stepA (hA : StepA) : PI.SzEatI.SzEatI := by
  classical
  intro K ce eps Ct CGam Cc CT2 PK
  obtain ⟨x0, hx0⟩ := hA K eps
  obtain ⟨C, hC, x1, hx1⟩ := UpperTheory.sum_log_mul_max_zero_le_of_odd_addOrderOf ce eps Ct CGam Cc CT2 PK
  have hc1 : 0 ≤ c1 ce := by unfold c1; positivity
  refine ⟨c1 ce + 1 + C, by positivity, max x0 x1, ?_⟩
  intro D L P hU hx hSz j hj S hS
  obtain ⟨hbb, hR0, hYR, hY1, hlog⟩ := hx0 D L hU.1 (le_trans (le_max_left _ _) hx) hSz
  have hX := hx1 D L P hU (le_trans (le_max_right _ _) hx) hSz j hj (S.filter fun p => IsCs D p) (by
    intro p hp
    obtain ⟨hpS, hcs⟩ := Finset.mem_filter.1 hp
    exact ⟨(hS p hpS).1, hcs.1, hcs.2.1, (hS p hpS).2.2.2⟩)
  have hXs : ∑ p ∈ S, Real.log p * EatX L ce j p ≤
      C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n) := by
    refine le_trans ?_ hX
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    unfold EatX
    split_ifs
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.log_natCast_nonneg p)
    · simp
  set Y := L.sc.X'' D.R.n with hYdef
  set f : ℝ := (D.R.f : ℝ) with hfdef
  have hf : 0 ≤ f := Nat.cast_nonneg _
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hpt : ∀ p ∈ S, Real.log p * (EatI L K ce j p -
      max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) ≤
      c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p := by
    intro p hp
    obtain ⟨hpr, -, -, hpY⟩ := hS p hp
    have h := prime_weighted_remainder_bound K ce D L hSz hbb j hj p hpr hpY
    unfold rest at h
    rw [mul_sub] at h
    linarith
  have hM : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y :=
    sum_log_p_over_p Y hY1 S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.2⟩)
  have hcard : (S.card : ℝ) ≤ Y :=
    card_le_of_le S Y (by linarith) (fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2.2⟩)
  calc ∑ p ∈ S, Real.log p * (EatI L K ce j p -
        max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)))
      ≤ ∑ p ∈ S, (c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p) :=
        Finset.sum_le_sum hpt
    _ = c1 ce * f * L.sc.b * (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)) + (S.card : ℝ) * (f * Rt L K) +
          ∑ p ∈ S, Real.log p * EatX L ce j p := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ c1 ce * f * L.sc.b * Real.log Y + Y * (f * Rt L K) + C * f * L.sc.b * Real.log Y := by
        have h0 : 0 ≤ c1 ce * f * L.sc.b := mul_nonneg (mul_nonneg hc1 hf) hb
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hM h0)
          (mul_le_mul_of_nonneg_right hcard (mul_nonneg hf hR0))) hXs
    _ = c1 ce * f * L.sc.b * Real.log Y + f * (Y * Rt L K) + C * f * L.sc.b * Real.log Y := by ring
    _ ≤ c1 ce * f * L.sc.b * Real.log Y + f * (L.sc.b * Real.log Y) + C * f * L.sc.b * Real.log Y := by
        refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hf)) le_rfl
        calc Y * Rt L K ≤ L.sc.b := hYR
          _ = L.sc.b * 1 := by ring
          _ ≤ L.sc.b * Real.log Y := mul_le_mul_of_nonneg_left hlog hb
    _ = (c1 ce + 1 + C) * f * L.sc.b * Real.log Y := by ring

end UpperTheory.G2
