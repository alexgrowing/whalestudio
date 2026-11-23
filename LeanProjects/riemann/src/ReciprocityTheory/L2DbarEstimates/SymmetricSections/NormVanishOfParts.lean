import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem growth_on_line (n m : ℕ) (C : ℝ) (t : ℂ) (w : V n) :
    max (C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)) 0 ≤
      max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by
  have hr : 0 ≤ ‖t • w‖ := norm_nonneg _
  have hP : (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) = (Real.sqrt (1 + ‖t • w‖ ^ 2)) ^ m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  have hs : Real.sqrt (1 + ‖t • w‖ ^ 2) ≤ (1 + ‖w‖) * (1 + ‖t‖) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [norm_smul]
    have ht := norm_nonneg t
    have hw := norm_nonneg w
    nlinarith [mul_nonneg ht hw, mul_nonneg (mul_nonneg ht hw) ht, mul_nonneg (mul_nonneg ht hw) hw]
  have hQ : (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) ≤ ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by
    rw [hP]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs m
  have hQ0 : 0 ≤ (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) := by positivity
  refine max_le ?_ (by positivity)
  calc C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)
      ≤ max C 0 * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0
    _ ≤ max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m :=
        mul_le_mul_of_nonneg_left hQ (le_max_right _ _)

theorem normVanish_of_parts (h1 : lineVanishStatement) (h2 : esymmZeroStatement)
    (h4 : symmDiffStatement.{u}) (h5 : symmVanishStatement.{u})
    (h6 : symmGrowthStatement.{u}) (h7 : lineFiniteStatement) :
    normVanishStatement.{u} := by
  intro n M _ z Δ δ m C u hΔ0 hcov hrange hdeg hholo hgrowth hvan x
  have hfin : ∀ w, (z ⁻¹' {w}).Finite := fun w => Set.finite_of_encard_le_coe (hdeg w)
  have key : ∀ k : ℕ, 1 ≤ k → fiberSymm n z u k (z x) = 0 := by
    intro k hk
    have hB : {t : ℂ | polyAt n Δ (t • z x) = 0}.Finite := h7 n Δ (z x) hΔ0
    have h1B : (1 : ℂ) ∉ {t : ℂ | polyAt n Δ (t • z x) = 0} := by
      simpa using hrange x
    have hlt : k * m < k * (m + 1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self m) hk
    have := h1 (fun t => fiberSymm n z u k (t • z x)) {t : ℂ | polyAt n Δ (t • z x) = 0}
      (2 ^ δ * (max C 0) ^ k * (1 + ‖z x‖) ^ (k * m)) (k * m) (k * (m + 1)) hB hlt ?_ ?_ ?_ 1 h1B
    · simpa using this
    ·
      intro t ht
      have hU : t • z x ∈ {w | polyAt n Δ w ≠ 0} := ht
      exact ((h4 n M z {w | polyAt n Δ w ≠ 0} u hcov (fun y => hrange y) (fun w _ => hfin w)
        hholo k (t • z x) hU).comp t (differentiableAt_id.smul_const (z x))).differentiableWithinAt
    ·
      intro t _
      have hg := h6 n M z u (fun v => C * (1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)) δ hgrowth hdeg k (t • z x)
      refine hg.trans ?_
      have hl := growth_on_line n m C t (z x)
      have hl' : (max (C * (1 + ‖t • z x‖ ^ 2) ^ ((m : ℝ) / 2)) 0) ^ k ≤
          (max C 0 * ((1 + ‖z x‖) * (1 + ‖t‖)) ^ m) ^ k :=
        pow_le_pow_left₀ (le_max_right _ _) hl k
      calc 2 ^ δ * (max (C * (1 + ‖t • z x‖ ^ 2) ^ ((m : ℝ) / 2)) 0) ^ k
          ≤ 2 ^ δ * (max C 0 * ((1 + ‖z x‖) * (1 + ‖t‖)) ^ m) ^ k :=
            mul_le_mul_of_nonneg_left hl' (by positivity)
        _ = 2 ^ δ * (max C 0) ^ k * (1 + ‖z x‖) ^ (k * m) * (1 + ‖t‖) ^ (k * m) := by
            rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m k]; ring
    ·
      have hv := h5 n M z {w | polyAt n Δ w ≠ 0} u 0 (m + 1) hcov hΔ0 (hfin 0) hvan k
      have ht : Tendsto (fun t : ℂ => t • z x) (𝓝 0) (𝓝 0) := by
        exact ((continuous_id.smul continuous_const).tendsto' (0 : ℂ) (0 : V n) (by simp) :
          Tendsto (fun t : ℂ => t • z x) (𝓝 0) (𝓝 0))
      refine (hv.comp_tendsto ht).trans ?_
      refine IsBigO.of_bound (‖z x‖ ^ (k * (m + 1))) (Eventually.of_forall fun t => ?_)
      simp [norm_smul, mul_pow, norm_pow, mul_comm]
  have hmem : u x ∈ fiberVals n z u (z x) := by
    unfold fiberVals
    rw [dif_pos (hfin (z x))]
    exact Multiset.mem_map.mpr ⟨x, by simp, rfl⟩
  exact h2 _ key (u x) hmem

end ReciprocityTheory.L2DbarEstimates.Norm
