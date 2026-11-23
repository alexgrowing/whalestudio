import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormIteratedFDerivWithinInvOneLe

open MeasureTheory Module
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def au (j : ℕ) : ℝ := j ! * j ! * 4 ^ j

theorem au_nonneg (j : ℕ) : 0 ≤ au j := by
  unfold au
  positivity

theorem contDiff_u (n : ℕ∞) : ContDiff ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).inv (fun y => by positivity)

theorem norm_iteratedFDeriv_w_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * au i * au (n - i)) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
  refine (norm_iteratedFDeriv_mul_le (N := (n : ℕ∞)) (contDiff_u n) (contDiff_u n) x le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := norm_iteratedFDeriv_u_le (V := V) i x
  have h2 := norm_iteratedFDeriv_u_le (V := V) (n - i) x
  have hq : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖
      ≤ (n.choose i : ℝ) * (au i * (1 + ‖x‖ ^ 2)⁻¹) * (au (n - i) * (1 + ‖x‖ ^ 2)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (au_nonneg i) hq))
    _ = (n.choose i : ℝ) * au i * au (n - i) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring

theorem inv_sq_le (x : V) : (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ ≤ 4 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hA : (0 : ℝ) < (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) := by positivity
  have hB : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
  have hr : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have h3 : ((1 + ‖x‖) ^ 2) ^ 2 ≤ (2 * (1 + ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [hr, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB]
  nlinarith [h3]

theorem decay_of_weight {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ ∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hEb 0 (Nat.zero_le _) 0)
  have hDw : D = fun x => ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) • E x := by
    funext x
    rw [hDE x, smul_smul]
    have hq : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    field_simp
    simp
  have hwc : ContDiff ℝ m (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) :=
    (contDiff_u m).mul (contDiff_u m)
  refine ⟨hDw ▸ hwc.smul hE, ?_⟩
  set Kw : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * au l * au (i - l) with hKw
  have hKw0 : ∀ i, 0 ≤ Kw i := fun i =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (au_nonneg _)) (au_nonneg _)
  set Cn : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Kw i * B with hCn
  have hCn0 : ∀ n, 0 ≤ Cn n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hKw0 i)) hB
  refine ⟨4 * ∑ n ∈ Finset.range (m + 1), Cn n, fun j hj x => ?_⟩
  have hq0 : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  have hstep : ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
    rw [hDw]
    refine (norm_iteratedFDeriv_smul_le (N := (j : ℕ∞)) (hwc.of_le (by exact_mod_cast hj))
      (hE.of_le (by exact_mod_cast hj)) x le_rfl).trans ?_
    rw [hCn, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ *
          ‖iteratedFDeriv ℝ (j - i) E x‖
        ≤ (j.choose i : ℝ) * (Kw i * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹)) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_w_le i x) (Nat.cast_nonneg _))
            (hEb (j - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKw0 i) hq0))
      _ = (j.choose i : ℝ) * Kw i * B * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring
  have hsum : Cn j ≤ ∑ n ∈ Finset.range (m + 1), Cn n :=
    Finset.single_le_sum (fun n _ => hCn0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  calc ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := hstep
    _ ≤ (∑ n ∈ Finset.range (m + 1), Cn n) * (4 * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
        mul_le_mul hsum (inv_sq_le x) hq0 (Finset.sum_nonneg fun n _ => hCn0 n)
    _ = 4 * (∑ n ∈ Finset.range (m + 1), Cn n) * (1 + ‖x‖) ^ (-(4 : ℝ)) := by ring

theorem smooth_decay_of_weighted [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (hV : finrank ℝ V ≤ 3)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ (∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  obtain ⟨hD, C, hC⟩ := decay_of_weight hE B hEb hDE
  refine ⟨hD, ⟨C, hC⟩, fun j hj1 hjm => integral_iteratedFDeriv_eq_zero hD C (fun i hi x => ?_) j hj1 hjm⟩
  refine (hC i hi x).trans ?_
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  gcongr
  · linarith [norm_nonneg x]
  · have : (finrank ℝ V : ℝ) ≤ 3 := by exact_mod_cast hV
    linarith

end Formalism.FourierDecayAlt.P5.HerC.Fou
