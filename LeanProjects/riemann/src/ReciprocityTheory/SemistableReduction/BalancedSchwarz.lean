import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace ReciprocityTheory.MultiplicativeHeights

open Metric Set

theorem bs_mem_of_gauge_lt_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (hs : IsOpen s) (hb : Balanced ℂ s) (h0 : (0 : E) ∈ s) {x : E} (hx : gauge s x < 1) :
    x ∈ s := by
  have habs : Absorbent ℝ s := absorbent_nhds_zero (hs.mem_nhds h0)
  obtain ⟨b, hb0, hb1, y, hy, rfl⟩ := exists_lt_of_gauge_lt habs hx
  have : (b : ℂ) • y ∈ s := hb.smul_mem (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; exact hb1.le) hy
  simpa [Complex.coe_smul] using this

theorem bs_key {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set E) (g : E → ℂ)
    (M : ℝ) (hs : IsOpen s) (hb : Balanced ℂ s) (hg : DifferentiableOn ℂ g s)
    (hM : ∀ w ∈ s, ‖g w‖ ≤ M) (h0 : (0 : E) ∈ s) (z : E) (R : ℝ) (hR : 1 < R)
    (hRt : R * gauge s z ≤ 1) : ‖g z - g 0‖ ≤ (M + ‖g 0‖) / R := by
  have hmaps : MapsTo (fun ζ : ℂ => ζ • z) (ball (0 : ℂ) R) s := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ
    apply bs_mem_of_gauge_lt_one hs hb h0
    rw [gauge_smul hb]
    calc ‖ζ‖ * gauge s z ≤ ‖ζ‖ * (1 / R) := by
          gcongr
          rw [le_div_iff₀ (by linarith)]; linarith
      _ < R * (1 / R) := by
          gcongr
      _ = 1 := by field_simp
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => g (ζ • z)) (ball (0 : ℂ) R) :=
    hg.comp (differentiableOn_id.smul_const z) hmaps
  have hm2 : MapsTo (fun ζ : ℂ => g (ζ • z)) (ball (0 : ℂ) R)
      (closedBall ((fun ζ : ℂ => g (ζ • z)) 0) (M + ‖g 0‖)) := by
    intro ζ hζ
    simp only [zero_smul, mem_closedBall, dist_eq_norm]
    calc ‖g (ζ • z) - g 0‖ ≤ ‖g (ζ • z)‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ M + ‖g 0‖ := by gcongr; exact hM _ (hmaps hζ)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_one]; exact hR
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm2 h1
  simpa [dist_eq_norm] using this

theorem balancedSchwarz_holds : BalancedSchwarzStatement := by
  intro E _ _ s g M hs hb hg hM z hz
  have h0 : (0 : E) ∈ s := by simpa using hb.smul_mem (a := (0 : ℂ)) (by simp) hz
  have ht0 : 0 ≤ gauge s z := gauge_nonneg z
  have ht1 : gauge s z < 1 := gauge_lt_one_of_mem_of_isOpen hs hz
  have hN : 0 ≤ M + ‖g 0‖ := by
    have := hM 0 h0; have := norm_nonneg (g 0); linarith
  rcases ht0.lt_or_eq with hpos | hzero
  · have := bs_key s g M hs hb hg hM h0 z (1 / gauge s z)
      (by rw [lt_div_iff₀ hpos]; linarith) (by field_simp; rfl)
    simpa [div_eq_mul_inv, mul_comm] using this
  · rw [← hzero, mul_zero]
    by_contra hne'
    have hne := not_le.mp hne'
    set d := ‖g z - g 0‖
    have hR : 1 < (M + ‖g 0‖) / d * 2 + 2 := by
      have : 0 ≤ (M + ‖g 0‖) / d * 2 := by positivity
      linarith
    have := bs_key s g M hs hb hg hM h0 z ((M + ‖g 0‖) / d * 2 + 2) hR
      (by rw [← hzero, mul_zero]; exact zero_le_one)
    rw [le_div_iff₀ (by linarith)] at this
    have h3 : d * ((M + ‖g 0‖) / d * 2 + 2) = 2 * (M + ‖g 0‖) + 2 * d := by
      field_simp
    nlinarith

end ReciprocityTheory.MultiplicativeHeights
