import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

namespace GlobalTheory.HessLevi

open Filter Topology Metric

theorem symm_of_hasFDerivAt_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {z : E} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hH : HasFDerivAt (fderiv ℝ φ) H z) (u v : E) : H u v = H v u := by
  by_cases hL : fderiv ℝ φ z = 0
  swap
  · have hev : ∀ᶠ y in 𝓝 z, fderiv ℝ φ y ≠ 0 := hH.continuousAt.eventually_ne hL
    refine second_derivative_symmetric_of_eventually_of_real (f := φ) ?_ hH u v
    filter_upwards [hev] with y hy
    have : DifferentiableAt ℝ φ y := by
      by_contra hd; exact hy (fderiv_zero_of_not_differentiableAt hd)
    exact this.hasFDerivAt
  by_cases h0 : ∀ a b, H a b = 0
  · rw [h0, h0]
  push_neg at h0
  obtain ⟨a0, w, ha⟩ := h0
  obtain ⟨x0, hx0⟩ : ∃ x0, 0 < H x0 w := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact ⟨-a0, by simpa using neg_pos.mpr h⟩
    · exact ⟨a0, h⟩
  have hx0ne : x0 ≠ 0 := by rintro rfl; simp at hx0
  have hnx0 : 0 < ‖x0‖ := norm_pos_iff.mpr hx0ne
  set κ : ℝ := H x0 w / (2 * ‖x0‖) with hκ
  have hκpos : 0 < κ := div_pos hx0 (by positivity)
  have hκx0 : κ * ‖x0‖ = H x0 w / 2 := by
    rw [hκ]; field_simp
  set c : ℝ := κ / (2 * (‖w‖ + 1)) with hc
  have hcpos : 0 < c := div_pos hκpos (by positivity)
  have hcw : c * ‖w‖ ≤ κ / 2 := by
    rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg w]
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ p ∈ ball z δ,
      ‖fderiv ℝ φ p - fderiv ℝ φ z - H (p - z)‖ ≤ c * ‖p - z‖ :=
    Metric.eventually_nhds_iff_ball.1 (hH.isLittleO.def hcpos)
  set C : Set E := {p | κ * ‖p - z‖ ≤ H (p - z) w} with hC
  have conv1 : Convex ℝ C := by
    intro p hp q hq a b ha hb hab
    simp only [hC, Set.mem_setOf_eq] at *
    have e : a • p + b • q - z = a • (p - z) + b • (q - z) := by
      calc a • p + b • q - z = a • p + b • q - (a + b) • z := by rw [hab, one_smul]
        _ = _ := by module
    rw [e]
    have hn : ‖a • (p - z) + b • (q - z)‖ ≤ a * ‖p - z‖ + b * ‖q - z‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hlin : H (a • (p - z) + b • (q - z)) w = a * H (p - z) w + b * H (q - z) w := by
      simp [map_add, map_smul]
    rw [hlin]
    calc κ * ‖a • (p - z) + b • (q - z)‖ ≤ κ * (a * ‖p - z‖ + b * ‖q - z‖) :=
          mul_le_mul_of_nonneg_left hn hκpos.le
      _ = a * (κ * ‖p - z‖) + b * (κ * ‖q - z‖) := by ring
      _ ≤ a * H (p - z) w + b * H (q - z) w := by
          gcongr
  set s : Set E := C ∩ ball z δ with hs
  have s_conv : Convex ℝ s := conv1.inter (convex_ball z δ)
  have hzs : z ∈ s := ⟨by simp [hC], mem_ball_self hδ⟩
  have hcont1 : Continuous fun p : E => κ * ‖p - z‖ := by fun_prop
  have hcont2 : Continuous fun p : E => H (p - z) w := by
    have : (fun p : E => H (p - z) w) = fun p => (H.flip w) (p - z) := by
      funext p; simp
    rw [this]; fun_prop
  have hne : (interior s).Nonempty := by
    set U : Set E := {p | κ * ‖p - z‖ < H (p - z) w} ∩ ball z δ with hU
    have hUo : IsOpen U := (isOpen_lt hcont1 hcont2).inter isOpen_ball
    have hUs : U ⊆ s := fun p hp => ⟨(show κ * ‖p - z‖ < H (p - z) w from hp.1).le, hp.2⟩
    set t : ℝ := δ / (2 * (‖x0‖ + 1)) with ht
    have htpos : 0 < t := div_pos hδ (by positivity)
    refine ⟨z + t • x0, interior_maximal hUs hUo ⟨?_, ?_⟩⟩
    · simp only [Set.mem_setOf_eq, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le,
        map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have : κ * (t * ‖x0‖) = t * (H x0 w / 2) := by rw [← hκx0]; ring
      rw [this]
      nlinarith
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le, ht]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg x0]
  have hzint : z ∉ interior s := by
    intro hz
    have hmem : s ∈ 𝓝 z := mem_interior_iff_mem_nhds.1 hz
    have htend : Tendsto (fun t : ℝ => z - t • x0) (𝓝[>] 0) (𝓝 z) := by
      have hc0 : Continuous fun t : ℝ => z - t • x0 := by fun_prop
      exact (hc0.tendsto' 0 z (by simp)).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), z - t • x0 ∈ s := htend hmem
    obtain ⟨t, hts, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have h1 := hts.1
    simp only [hC, Set.mem_setOf_eq, sub_sub_cancel_left, norm_neg, norm_smul, map_neg,
      map_smul, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h1
    have htp : (0 : ℝ) < t := htpos
    have : 0 ≤ κ * (‖t‖ * ‖x0‖) := by positivity
    nlinarith [mul_pos htp hx0]
  have hf : ∀ x ∈ interior s, HasFDerivAt φ (fderiv ℝ φ x) x := by
    intro x hx
    have hxs : x ∈ s := interior_subset hx
    have hxz : x ≠ z := by rintro rfl; exact hzint hx
    refine DifferentiableAt.hasFDerivAt ?_
    by_contra hd
    have hb := hball x hxs.2
    rw [fderiv_zero_of_not_differentiableAt hd, hL, sub_zero, zero_sub, norm_neg] at hb
    have h1 : κ * ‖x - z‖ ≤ H (x - z) w := hxs.1
    have h2 : H (x - z) w ≤ ‖H (x - z)‖ * ‖w‖ :=
      (le_abs_self _).trans ((H (x - z)).le_opNorm w)
    have h3 : ‖H (x - z)‖ * ‖w‖ ≤ c * ‖x - z‖ * ‖w‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have h4 : c * ‖x - z‖ * ‖w‖ ≤ κ / 2 * ‖x - z‖ := by
      rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right hcw (norm_nonneg _)
    have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    nlinarith
  exact s_conv.second_derivative_within_at_symmetric hne hf hzs hH.hasFDerivWithinAt u v

theorem polar {n : ℕ} {H K : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ}
    (hsH : ∀ a b, H a b = H b a) (hsK : ∀ a b, K a b = K b a)
    (hd : ∀ w, H w w + H (Complex.I • w) (Complex.I • w) =
      K w w + K (Complex.I • w) (Complex.I • w)) (a b : Fin n → ℂ) :
    H a b + H (Complex.I • a) (Complex.I • b) = K a b + K (Complex.I • a) (Complex.I • b) := by
  have h1 := hd (a + b)
  have h2 := hd a
  have h3 := hd b
  simp only [smul_add, map_add, ContinuousLinearMap.add_apply] at h1
  rw [hsH b a, hsH (Complex.I • b) (Complex.I • a), hsK b a,
    hsK (Complex.I • b) (Complex.I • a)] at h1
  linarith

end GlobalTheory.HessLevi

namespace GlobalTheory.HessLevi

theorem hessC_eq_of_levi_eq {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ z) (hlev : ∀ w, levi φ z w = levi ψ z w) :
    hessC φ z = hessC ψ z := by
  have hsK : ∀ a b, fderiv ℝ (fderiv ℝ ψ) z a b = fderiv ℝ (fderiv ℝ ψ) z b a :=
    hψ.isSymmSndFDerivAt (by simp)
  have hsH : ∀ a b, fderiv ℝ (fderiv ℝ φ) z a b = fderiv ℝ (fderiv ℝ φ) z b a := by
    by_cases hd : DifferentiableAt ℝ (fderiv ℝ φ) z
    · exact symm_of_hasFDerivAt_fderiv hd.hasFDerivAt
    · intro a b; rw [fderiv_zero_of_not_differentiableAt hd]; rfl
  have hd : ∀ w, fderiv ℝ (fderiv ℝ φ) z w w +
        fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w) =
      fderiv ℝ (fderiv ℝ ψ) z w w + fderiv ℝ (fderiv ℝ ψ) z (Complex.I • w) (Complex.I • w) := by
    intro w
    have := hlev w
    simp only [levi] at this
    linarith
  have key := polar hsH hsK hd
  ext i j
  simp only [hessC]
  have k1 := key (Pi.single i 1) (Pi.single j 1)
  have k2 := key (Pi.single i 1) (Complex.I • Pi.single j 1)
  have hII : Complex.I • Complex.I • (Pi.single j 1 : Fin n → ℂ) = -Pi.single j 1 := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hII, map_neg, map_neg] at k2
  have k2' : fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) (Complex.I • Pi.single j 1) -
        fderiv ℝ (fderiv ℝ φ) z (Complex.I • Pi.single i 1) (Pi.single j 1) =
      fderiv ℝ (fderiv ℝ ψ) z (Pi.single i 1) (Complex.I • Pi.single j 1) -
        fderiv ℝ (fderiv ℝ ψ) z (Complex.I • Pi.single i 1) (Pi.single j 1) := by
    linarith
  rw [k1, k2']

end GlobalTheory.HessLevi
