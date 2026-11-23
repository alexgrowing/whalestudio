import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_apply_le_of_laplacian_lower_bound :
    ∀ (d : ℕ) (c C : ℝ) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∃ C' : ℝ, ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (A : Fin d → Module.End ℂ M), (∀ i, ∀ x ∈ V, A i x ∈ V) → (∀ i, ∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (A i x)) (j y) + inner ℂ (j x) (j (A i y)) = 0) → ∀ v ∈ V, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re → (∀ i, ε i = -1 → ‖j (A i v)‖ ≤ C * ‖j v‖) → ∀ i, ‖j (A i v)‖ ≤ C' * ‖j v‖ := by
  intro d c C ε hε
  refine ⟨Real.sqrt (|c| + (d + 1) * C ^ 2), ?_⟩
  intro M H _ _ _ _ j V A hA hskew v hv hcas hC i
  have h1 : ∀ k, inner ℂ (j v) (j (A k (A k v))) = -((‖j (A k v)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have h := hskew k v hv (A k v) (hA k v hv)
    rw [inner_self_eq_norm_sq_to_K] at h
    push_cast
    exact eq_neg_of_add_eq_zero_right h
  have h2 : (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re
      = -∑ k, ε k * ‖j (A k v)‖ ^ 2 := by
    rw [map_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right, h1 k, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [h2] at hcas
  have h3 : ∀ k, ε k = -1 → ‖j (A k v)‖ ^ 2 ≤ C ^ 2 * ‖j v‖ ^ 2 := by
    intro k hk
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC k hk) 2
  have hCN : 0 ≤ C ^ 2 * ‖j v‖ ^ 2 := by positivity
  have h4 : ∀ k, 0 ≤ ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2 := by
    intro k
    rcases hε k with hk | hk
    · rw [hk]; positivity
    · have := h3 k hk
      rw [hk]; linarith
  have h5 : ε i * ‖j (A i v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2
      ≤ ∑ k, (ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2) :=
    Finset.single_le_sum (f := fun k => ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2)
      (fun k _ => h4 k) (Finset.mem_univ i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h5
  have hc : c * ‖j v‖ ^ 2 ≤ |c| * ‖j v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  have hc0 : 0 ≤ |c| * ‖j v‖ ^ 2 := by positivity
  have hd : 0 ≤ (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) := by positivity
  have h6 : ‖j (A i v)‖ ^ 2 ≤ (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2 := by
    have e : (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2
        = |c| * ‖j v‖ ^ 2 + (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) + C ^ 2 * ‖j v‖ ^ 2 := by ring
    rw [e]
    rcases hε i with hk | hk
    · rw [hk] at h5; linarith
    · have := h3 i hk
      linarith
  have h7 := Real.le_sqrt_of_sq_le h6
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at h7
