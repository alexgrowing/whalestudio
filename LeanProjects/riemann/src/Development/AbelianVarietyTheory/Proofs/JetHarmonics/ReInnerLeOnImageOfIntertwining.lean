import Mathlib

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem re_inner_sum_eigen_le {N ι : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [Fintype ι] (B : N →ₗ[ℂ] N) (hB : B.IsSymmetric) (C : ℝ) (v : ι → N) (l : ι → ℝ)
    (hv : ∀ i, B (v i) = (l i : ℂ) • v i) (hl : ∀ i, l i ≤ C) :
    (⟪∑ i, v i, B (∑ i, v i)⟫_ℂ).re ≤ C * ‖∑ i, v i‖ ^ 2 := by
  have key : ∀ i j, ((C : ℂ) - l j) * ⟪v i, v j⟫_ℂ =
      ⟪((√(C - l i) : ℝ) : ℂ) • v i, ((√(C - l j) : ℝ) : ℂ) • v j⟫_ℂ := by
    intro i j
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
    by_cases h : l i = l j
    · rw [h, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.2 (hl j))]
      push_cast
      rfl
    · have h1 := hB (v i) (v j)
      rw [hv, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h2 : ((l i : ℂ) - l j) * ⟪v i, v j⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      have h3 : ((l i : ℂ) - l j) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast h
      have h4 : ⟪v i, v j⟫_ℂ = 0 := (mul_eq_zero.1 h2).resolve_left h3
      rw [h4, mul_zero, mul_zero]
  have hsum : (C : ℂ) * ⟪∑ i, v i, ∑ i, v i⟫_ℂ - ⟪∑ i, v i, B (∑ i, v i)⟫_ℂ =
      ⟪∑ i, ((√(C - l i) : ℝ) : ℂ) • v i, ∑ i, ((√(C - l i) : ℝ) : ℂ) • v i⟫_ℂ := by
    rw [map_sum]
    simp only [sum_inner, inner_sum, ← key, hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, sub_mul]
  have hre := congrArg Complex.re hsum
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re] at hre
  nlinarith [sq_nonneg ‖∑ i, ((√(C - l i) : ℝ) : ℂ) • v i‖]

theorem re_inner_le_on_image_of_intertwining :
    ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
      [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T)
      (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) →
      (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) →
      ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  intro T N _ _ _ _ _ Φ A B C hA hB hΦ hC x
  set b := hA.eigenvectorBasis (n := Module.finrank ℂ T) rfl with hb
  set l := hA.eigenvalues (n := Module.finrank ℂ T) rfl with hl
  have hAb : ∀ i, A (b i) = (l i : ℂ) • b i := fun i => hA.apply_eigenvectorBasis rfl i
  have hle : ∀ i, l i ≤ C := by
    intro i
    have h := hC (b i)
    rw [hAb, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
    simpa using h
  have hx : Φ x = ∑ i, Φ (b.repr x i • b i) := by
    rw [← map_sum, b.sum_repr]
  rw [hx]
  refine re_inner_sum_eigen_le B hB C _ l (fun i => ?_) hle
  rw [← hΦ, map_smul A, hAb, smul_comm, map_smul]

end GlobalTheory
