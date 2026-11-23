import Mathlib

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Finset
open scoped ComplexConjugate InnerProductSpace

theorem norm_sq_comb {κ : Type} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J : Finset κ) (b : κ → ℂ)
    (y : κ → W) :
    ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ J, ∑ l ∈ J, conj (b j) * b l * ⟪y j, y l⟫_ℂ := by
  rw [show ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ⟪∑ j ∈ J, b j • y j, ∑ j ∈ J, b j • y j⟫_ℂ by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem sum_sq_le_sq_sum {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hx j) (mem_univ i)) (hx i)

theorem norm_sum_le_of_gram {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ P Q, k P Q = ⟪v P, v Q⟫_ℂ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = ∑ i, (c i : ℂ) * ⟪Y i (P l), Y i (P j)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ := by
  have h1 : ((‖∑ j ∈ J, a j • v (P j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_comb]
    calc ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * ⟪v (P j), v (P l)⟫_ℂ
        = ∑ j ∈ J, ∑ l ∈ J, ∑ i, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
          rw [← hv, hk j hj l hl, mul_sum]
          refine sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j ∈ J, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          exact (sum_congr rfl fun j _ => sum_comm).trans sum_comm
      _ = ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
          refine sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_mul, norm_sq_comb, mul_sum, sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [Complex.conj_conj]
          ring
  have h2 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 := by
    exact_mod_cast h1
  have h3 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 ≤ (∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
    rw [h2]
    have : ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 =
        ∑ i, (√(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hc i)]
    rw [this]
    exact sum_sq_le_sq_sum _ fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ :=
    sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (∑ j ∈ J, a j • v (P j))]

end Formalism.FourierDecayAlt.P.GermRateSplit
