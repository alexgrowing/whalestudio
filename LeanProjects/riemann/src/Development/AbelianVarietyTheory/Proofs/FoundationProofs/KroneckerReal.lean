import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.TailIntegralOfSummatory

noncomputable def recSum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Icc 1 N, a n / (n : ℂ)

lemma recSum_succ (a : ℕ → ℂ) (N : ℕ) :
    recSum a (N + 1) = recSum a N + a (N + 1) / ((N + 1 : ℕ) : ℂ) := by
  unfold recSum
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma sum_eq (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n = N * recSum a N - ∑ k ∈ range N, recSum a k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, recSum_succ]
    have h : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    field_simp
    push_cast
    ring

lemma kronecker (a : ℕ → ℂ) (S : ℂ) (h : Tendsto (recSum a) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n) / (N : ℂ)) atTop (𝓝 0) := by
  have h2 := h.sub h.cesaro_smul
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sum_eq, Complex.real_smul]
  push_cast
  field_simp

lemma kronecker_real (a : ℕ → ℂ) (S : ℂ) (h : Tendsto (recSum a) atTop (𝓝 S)) :
    Tendsto (fun U : ℝ => psum a U / (U : ℂ)) atTop (𝓝 0) := by
  have h1 := (kronecker a S h).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 : Tendsto (fun U : ℝ => (((⌊U⌋₊ : ℝ) / U : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_nat_floor_div_atTop (R := ℝ))
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  have hN : 0 < ⌊U⌋₊ := Nat.floor_pos.2 hU
  have hN' : (⌊U⌋₊ : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Function.comp, psum]
  push_cast
  field_simp

lemma sum_Icc_zero (a : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then 0 else a k) = ∑ k ∈ Icc 1 N, a k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    simp

lemma integral_eq (a : ℕ → ℂ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, psum a u / (u : ℂ) ^ 2 =
      (recSum a ⌊U⌋₊ - psum a U / U) - (recSum a ⌊y⌋₊ - psum a y / y) := by
  have hd : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t : ℝ => ((t : ℂ))⁻¹) (-(((t : ℂ)) ^ 2)⁻¹) t := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    exact (hasDerivAt_inv ht').comp_ofReal
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => by
    have := ht.1
    intro h0
    linarith
  have hint : IntegrableOn (deriv (fun t : ℝ => ((t : ℂ))⁻¹)) (Set.Icc y U) := by
    have hc : ContinuousOn (fun t : ℝ => -(((t : ℂ)) ^ 2)⁻¹) (Set.Icc y U) := by
      refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) ?_)
      intro t ht
      exact pow_ne_zero _ (by exact_mod_cast hne t ht)
    refine (hc.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    exact ((hd t (hne t ht)).deriv).symm
  have key := sum_mul_eq_sub_sub_integral_mul (f := fun t : ℝ => ((t : ℂ))⁻¹)
    (fun k => if k = 0 then 0 else a k) (a := y) (b := U) (by linarith) hU
    (fun t ht => (hd t (hne t ht)).differentiableAt) hint
  simp only [sum_Icc_zero] at key
  have hfl : ⌊y⌋₊ ≤ ⌊U⌋₊ := Nat.floor_le_floor hU
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, (((k : ℝ) : ℂ))⁻¹ * (if k = 0 then 0 else a k)
      = recSum a ⌊U⌋₊ - recSum a ⌊y⌋₊ := by
    have e : ∀ N : ℕ, recSum a N = ∑ n ∈ Ioc 0 N, a n / (n : ℂ) := fun N => by
      unfold recSum
      rfl
    rw [e, e, eq_sub_iff_add_eq', ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≠ 0 := by
      have := (Finset.mem_Ioc.1 hk).1
      omega
    rw [if_neg this, div_eq_inv_mul]
    simp
  have hI : ∫ t in Set.Ioc y U, deriv (fun t : ℝ => ((t : ℂ))⁻¹) t * ∑ k ∈ Icc 1 ⌊t⌋₊, a k
      = -∫ u in y..U, psum a u / (u : ℂ) ^ 2 := by
    rw [intervalIntegral.integral_of_le hU, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have := (hd t (hne t ⟨ht.1.le, ht.2⟩)).deriv
    simp only [this, psum]
    ring
  rw [hL, hI] at key
  simp only [psum] at key ⊢
  linear_combination -key

theorem tail_integral : Formalism.HermitianLattices.GL2PrimeSums.SmoothedRemainderIntegralFormula := by
  intro a S h y hy
  have h' : Tendsto (recSum a) atTop (𝓝 S) := h
  refine ⟨(S - 0) - (recSum a ⌊y⌋₊ - psum a y / y), ?_, ?_⟩
  · have h1 := ((h'.comp (tendsto_nat_floor_atTop (α := ℝ))).sub
      (kronecker_real a S h')).sub_const (recSum a ⌊y⌋₊ - psum a y / y)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    rw [integral_eq a hy hU]
    rfl
  · have hy0 : (y : ℂ) ≠ 0 := by
      have : y ≠ 0 := by linarith
      exact_mod_cast this
    have e : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)
        = y * recSum a ⌊y⌋₊ - psum a y := by
      unfold recSum psum
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    unfold Gchi
    rw [e]
    field_simp
    ring

end GlobalTheory.TailIntegralOfSummatory
