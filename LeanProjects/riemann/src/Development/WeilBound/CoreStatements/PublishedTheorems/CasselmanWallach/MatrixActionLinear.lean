import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegativeSymmetric

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hU a b (E b a x) y, hU b a x (E b a y)]
  simp [adjSign, hab]

theorem re_inner_casK_nonneg (hU : IsInfUnitary ε E) (x : V) : 0 ≤ (⟪x, casimirK ε E x⟫_ℂ).re := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply,
    inner_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b hb => ?_
  have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
  have h := hU b a x (E b a x)
  simp only [ReciprocityTheory.ChartRestriction.DS.adjSign, hb', if_true, one_mul] at h
  rw [← h]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := E b a x))

theorem eig_nonneg (hU : IsInfUnitary ε E) {μ : ℝ} {v : V} (hv : v ≠ 0) (h : Eig ε E μ v) : 0 ≤ μ := by
  have h2 := re_inner_casK_nonneg hU v
  rw [show casimirK ε E v = (μ : ℂ) • v from h, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : 0 ≤ μ * ‖v‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h2
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  by_contra hμ
  push_neg at hμ
  nlinarith [mul_neg_of_neg_of_pos hμ hn]

end PositivityTheory.CW.CasimirNonnegativeSymmetric

namespace PositivityTheory.CW

open CasimirNonnegativeSymmetric in
theorem e3a : CasimirPowerSurjectiveSymmetric := by
  intro k ε V _ _ E _ hU hM m
  set a := 1 + casimirK ε E with ha_def
  have ha : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
    intro x y
    simp only [ha_def, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right,
      casK_symm hU]
  have hsymm : ∀ j : ℕ, ∀ x y : V, ⟪(a ^ j) x, y⟫_ℂ = ⟪x, (a ^ j) y⟫_ℂ := by
    intro j
    induction j with
    | zero => intro x y; simp
    | succ j ih =>
      intro x y
      calc ⟪(a ^ (j + 1)) x, y⟫_ℂ = ⟪(a ^ j) (a x), y⟫_ℂ := by rw [pow_succ, Module.End.mul_apply]
        _ = ⟪a x, (a ^ j) y⟫_ℂ := ih _ _
        _ = ⟪x, a ((a ^ j) y)⟫_ℂ := ha _ _
        _ = ⟪x, (a ^ (j + 1)) y⟫_ℂ := by rw [pow_succ', Module.End.mul_apply]
  refine ⟨?_, hsymm m⟩
  have hrange : LinearMap.range (a ^ m) = ⊤ := by
    rw [eq_top_iff, ← hM.span, Submodule.span_le]
    rintro v ⟨μ, hv⟩
    show v ∈ LinearMap.range (a ^ m)
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    have hμ : 0 ≤ μ := eig_nonneg hU h0 hv
    have h1 : a v = (1 + (μ : ℂ)) • v := by
      simp [ha_def, add_smul, show casimirK ε E v = (μ : ℂ) • v from hv]
    have hav : ∀ j : ℕ, (a ^ j) v = ((1 + (μ : ℂ)) ^ j) • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, ← pow_succ']
    have hne1 : (1 + (μ : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact_mod_cast (by linarith : (0 : ℝ) < 1 + μ).ne'
    have hne : (1 + (μ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ hne1
    refine LinearMap.mem_range.2 ⟨((1 + (μ : ℂ)) ^ m)⁻¹ • v, ?_⟩
    rw [map_smul, hav, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact LinearMap.range_eq_top.1 hrange

end PositivityTheory.CW
