import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mollify_converges_C2_rate :
    ∀ (D : ℕ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D) (V K : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V → ContDiffOn ℝ ∞ u V → (∀ᶠ t in 𝓝[>] (0 : ℝ), Set.EqOn (w t) u V) → TendstoUniformlyOn (fun t => ReciprocityTheory.AnForm.A.molli ρ t (w t)) (u) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) (fderiv ℝ (u)) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)))) (fderiv ℝ (fderiv ℝ (u))) (𝓝[>] 0) K ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K, ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ (u) z‖ ≤ M * t := by
  intro D ρ V K u w hV hK hKV hu hw
  obtain ⟨C, ε₀, hε₀, hC⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ V K u hV
    (by exact_mod_cast contDiffOn_infty.1 hu 3) hK hKV
  have hsmallt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε₀ / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K,
      |ReciprocityTheory.AnForm.A.molli ρ t (w t) z - u z| ≤ C * t ∧
      ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ u z‖ ≤ C * t ∧
      ‖fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) z - fderiv ℝ (fderiv ℝ u) z‖
        ≤ C * t := by
    filter_upwards [self_mem_nhdsWithin, hsmallt, hw] with t ht htε hwt z hz
    have ht0 : 0 < t := ht
    have hz2 : z ∈ ReciprocityTheory.AnForm.A.shrink V (2 * t) :=
      (hC (2 * t) (by linarith) (by linarith) z hz).1
    obtain ⟨-, h0, h1, h2⟩ := hC t ht0 (by linarith) z hz
    have hev : ReciprocityTheory.AnForm.A.molli ρ t (w t) =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.molli ρ t u := by
      filter_upwards [ball_mem_nhds z ht0] with y hy
      refine ReciprocityTheory.AnForm.A.molli_congr ρ ht0 (U := V) ?_ hwt
      intro x hx
      apply hz2
      rw [mem_closedBall] at hx ⊢
      rw [mem_ball] at hy
      linarith [dist_triangle x y z]
    rw [hev.eq_of_nhds, hev.fderiv_eq, hev.fderiv.fderiv_eq]
    exact ⟨h0, h1, h2⟩
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ t in 𝓝[>] (0 : ℝ), C * t < δ := by
    intro δ hδ
    have h : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
      have h' : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    exact h.eventually (Iio_mem_nhds hδ)
  refine ⟨?_, ?_, ?_, C, key.mono fun t ht z hz => (ht z hz).2.1⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (ht z hz).1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.2 htδ

end GlobalTheory.CompanionTheory.Ar.Giv
