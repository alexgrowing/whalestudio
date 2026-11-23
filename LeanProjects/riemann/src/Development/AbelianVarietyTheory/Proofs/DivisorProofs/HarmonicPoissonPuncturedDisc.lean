import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExtA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff

namespace GlobalTheory

open Real InnerProductSpace ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

theorem punct_le_zero_of_meanValue {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn u (closedBall 0 R \ {0}))
    (hs : ∀ ζ ∈ sphere (0 : ℂ) R, u ζ = 0)
    (hm : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) R \ {0} → circleAverage u a s = u a)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ closedBall (0 : ℂ) R, z ≠ 0 → u z ≤ K - ε * log ‖z‖)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) (hw0 : w ≠ 0) : u w ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  set γ := u w with hγ
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hwR : ‖w‖ < R := mem_ball_zero_iff.1 hw
  set L := log R - log ‖w‖ with hL
  set ε := γ / (4 * (|L| + 1)) with hε
  set δ := γ / (4 * (R ^ 2 + 1)) with hδ
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 < δ := by positivity
  have hεL : ε * L < γ / 4 := by
    have : ε * (|L| + 1) = γ / 4 := by rw [hε]; field_simp
    nlinarith [le_abs_self L]
  have hδr : δ * R ^ 2 < γ / 4 := by
    have : δ * (R ^ 2 + 1) = γ / 4 := by rw [hδ]; field_simp
    nlinarith
  set E : Finset ℂ := {0} with hE
  have hEc : (↑E : Set ℂ) = {0} := by simp [hE]
  set k : ℂ → ℝ := fun ζ => u ζ + pert E 0 ε δ ζ with hk
  have hpe : ∀ ζ, pert E 0 ε δ ζ = ε * log ‖ζ‖ + δ * ‖ζ‖ ^ 2 := by
    intro ζ; simp [pert, hE]
  have hkw : k w = γ + ε * log ‖w‖ + δ * ‖w‖ ^ 2 := by
    simp only [hk, hpe, hγ]; ring
  obtain ⟨K, hK⟩ := hg (ε / 2) (by positivity)
  set T := k w - K - δ * R ^ 2 with hT
  refine mp_core (k := k) (c := 0) (ζ0 := w) (r := R) (E := E) (η := exp (2 * T / ε))
    (ball_subset_closedBall hw) (by simp [hE, hw0]) (exp_pos _) ?_ ?_ ?_ ?_
  · rw [hEc]
    refine hc.add ((pert_continuousOn E 0 ε δ).mono ?_)
    intro x hx; rw [hEc]; exact hx.2
  · intro ζ hζ
    have hn : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
    simp only [hk, hpe, hs ζ hζ, hn]
    have : ε * log R = ε * L + ε * log ‖w‖ := by rw [hL]; ring
    have : 0 ≤ δ * ‖w‖ ^ 2 := by positivity
    linarith
  · intro e he ζ hζ hd0 hd
    rw [hEc] at hζ
    have he0 : e = 0 := by simpa [hE] using he
    subst he0
    have hζ0 : ζ ≠ 0 := hζ.2
    have hζn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
    rw [dist_zero_right] at hd
    have hlog : log ‖ζ‖ < 2 * T / ε := (log_lt_iff_lt_exp hζn).2 hd
    have h1 : (ε / 2) * log ‖ζ‖ < T := by
      have := mul_lt_mul_of_pos_left hlog (by positivity : (0 : ℝ) < ε / 2)
      have e : ε / 2 * (2 * T / ε) = T := by field_simp
      linarith
    have hu := hK ζ hζ.1 hζ0
    have hq : ‖ζ‖ ^ 2 ≤ R ^ 2 := by
      have := mem_closedBall_zero_iff.1 hζ.1
      gcongr
    have hq' : δ * ‖ζ‖ ^ 2 ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left hq hδ0.le
    have hkζ : k ζ = u ζ + (ε * log ‖ζ‖ + δ * ‖ζ‖ ^ 2) := by simp only [hk, hpe]
    rw [hkζ]
    have : ε * log ‖ζ‖ = (ε / 2) * log ‖ζ‖ + (ε / 2) * log ‖ζ‖ := by ring
    linarith
  · intro a s hs0 hsub
    rw [hEc] at hsub
    have ha0 : a ∉ E := by
      rw [← Finset.mem_coe, hEc]; exact (hsub (mem_closedBall_self hs0.le)).2
    have hFs : ∀ f ∈ E, f ∉ sphere a s := by
      intro f hf hfs
      rw [← Finset.mem_coe, hEc] at hf
      exact (hsub (sphere_subset_closedBall hfs)).2 hf
    obtain ⟨hpi, hpm⟩ := pert_submean (c := 0) (δ := δ) hs0 hε0.le ha0 hFs
    have hsB : sphere a |s| ⊆ closedBall (0 : ℂ) R \ {0} := by
      rw [abs_of_pos hs0]
      intro x hx
      have := hsub (sphere_subset_closedBall hx)
      exact ⟨ball_subset_closedBall this.1, this.2⟩
    have hui : CircleIntegrable u a s := (hc.mono hsB).circleIntegrable'
    have hav : circleAverage k a s = circleAverage u a s + circleAverage (pert E 0 ε δ) a s :=
      circleAverage_fun_add hui hpi
    rw [hav, hm a s hs0 hsub]
    have : 0 < δ * s ^ 2 := by positivity
    simp only [hk]
    linarith

end GlobalTheory

namespace GlobalTheory

open Real InnerProductSpace ReciprocityTheory.AnForm.A

theorem harmonic_punctured_eq_poissonInt :
    ∀ (R : ℝ) (f : ℂ → ℝ), 0 < R → R ≤ 1 →
      InnerProductSpace.HarmonicOnNhd f (Metric.closedBall 0 R \ {0}) →
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) R, z ≠ 0 →
        |f z| ≤ K - ε * Real.log ‖z‖) →
      ∀ w ∈ Metric.ball (0 : ℂ) R, w ≠ 0 → f w = ReciprocityTheory.AnForm.A.poissonInt f R w := by
  classical
  intro R f hR _ hf hgrow w hw hw0
  have hsph : sphere (0 : ℂ) R ⊆ closedBall 0 R \ {0} := fun x hx =>
    ⟨sphere_subset_closedBall hx, by
      intro h0
      rw [Set.mem_singleton_iff] at h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hx
      exact hR.ne hx⟩
  have hfc : ContinuousOn f (closedBall 0 R \ {0}) := hf.continuousOn
  have hgs : ContinuousOn f (sphere 0 R) := hfc.mono hsph
  set Φ : ℂ → ℝ := fun v ↦ if v ∈ ball (0 : ℂ) R then poissonInt f R v else f v with hΦ
  have hΦb : ∀ v ∈ ball (0 : ℂ) R, Φ v = poissonInt f R v := fun v hv ↦ by
    rw [hΦ]; exact if_pos hv
  have hΦs : ∀ v ∈ sphere (0 : ℂ) R, Φ v = f v := fun v hv ↦ by
    have : v ∉ ball (0 : ℂ) R := by
      rw [mem_sphere_zero_iff_norm] at hv
      simp [hv]
    rw [hΦ]; exact if_neg this
  have hH : ∀ v ∈ ball (0 : ℂ) R, HarmonicAt Φ v := fun v hv ↦ by
    have he : Φ =ᶠ[𝓝 v] poissonInt f R := by
      filter_upwards [isOpen_ball.mem_nhds hv] with x hx using hΦb x hx
    rw [harmonicAt_congr_nhds he]
    exact poissonInt_harmonicAt hR hgs hv
  have hΦc : ContinuousOn Φ (closedBall 0 R) := by
    rw [← ball_union_sphere]
    intro x hx
    rcases hx with hx | hx
    · exact (hH x hx).1.continuousAt.continuousWithinAt
    · rw [continuousWithinAt_union]
      constructor
      · have ht := poissonInt_tendsto hR hgs hx
        rw [ContinuousWithinAt, hΦs x hx]
        exact ht.congr' (eventually_nhdsWithin_of_forall fun v hv ↦ (hΦb v hv).symm)
      · exact (hgs x hx).congr (fun v hv ↦ hΦs v hv) (hΦs x hx)
  obtain ⟨B, hB⟩ : ∃ B, ∀ ζ ∈ closedBall (0 : ℂ) R, |Φ ζ| ≤ B := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hΦc
    exact ⟨M, fun ζ hζ ↦ by simpa [Real.norm_eq_abs] using hM ζ hζ⟩
  have hmv : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) R \ {0} →
      CircleIntegrable f a s ∧ CircleIntegrable Φ a s ∧
      circleAverage f a s = f a ∧ circleAverage Φ a s = Φ a := by
    intro a s hs hsub
    have hsB : sphere a |s| ⊆ closedBall (0 : ℂ) R \ {0} := by
      rw [abs_of_pos hs]
      intro x hx
      have := hsub (sphere_subset_closedBall hx)
      exact ⟨ball_subset_closedBall this.1, this.2⟩
    refine ⟨(hfc.mono hsB).circleIntegrable', (hΦc.mono (hsB.trans Set.diff_subset)).circleIntegrable',
      ?_, ?_⟩
    · apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      rw [abs_of_pos hs]
      intro x hx
      have := hsub hx
      exact hf x ⟨ball_subset_closedBall this.1, this.2⟩
    · apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      rw [abs_of_pos hs]
      exact fun x hx ↦ hH x (hsub hx).1
  have hcu : ContinuousOn (fun z ↦ f z - Φ z) (closedBall 0 R \ {0}) :=
    hfc.sub (hΦc.mono Set.diff_subset)
  have h1 : f w - Φ w ≤ 0 := by
    refine punct_le_zero_of_meanValue (u := fun z ↦ f z - Φ z) hR hcu ?_ ?_ ?_ hw hw0
    · intro ζ hζ; simp [hΦs ζ hζ]
    · intro a s hs hsub
      obtain ⟨i1, i2, e1, e2⟩ := hmv a s hs hsub
      rw [circleAverage_fun_sub i1 i2, e1, e2]
    · intro ε hε
      obtain ⟨K, hK⟩ := hgrow ε hε
      refine ⟨K + B, fun z hz hz0 ↦ ?_⟩
      have a1 := hK z hz hz0
      have a2 := hB z hz
      have a3 := le_abs_self (f z)
      have a4 := neg_abs_le (Φ z)
      linarith
  have h2 : Φ w - f w ≤ 0 := by
    refine punct_le_zero_of_meanValue (u := fun z ↦ Φ z - f z) hR
      ((hΦc.mono Set.diff_subset).sub hfc) ?_ ?_ ?_ hw hw0
    · intro ζ hζ; simp [hΦs ζ hζ]
    · intro a s hs hsub
      obtain ⟨i1, i2, e1, e2⟩ := hmv a s hs hsub
      rw [circleAverage_fun_sub i2 i1, e1, e2]
    · intro ε hε
      obtain ⟨K, hK⟩ := hgrow ε hε
      refine ⟨K + B, fun z hz hz0 ↦ ?_⟩
      have a1 := hK z hz hz0
      have a2 := hB z hz
      have a3 := neg_abs_le (f z)
      have a4 := le_abs_self (Φ z)
      linarith
  rw [← hΦb w hw]
  linarith

end GlobalTheory
