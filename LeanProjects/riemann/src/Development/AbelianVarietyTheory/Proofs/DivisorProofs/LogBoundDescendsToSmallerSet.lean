import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff

namespace GlobalTheory

theorem poissonInt_update_bound (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (R r : ℝ)
    (f : (Fin e → ℂ) → ℝ) (hr : 0 < r) (hrR : r < R) (hci : c i = 0) (hiS : i ∉ S)
    (hf : ContinuousOn f {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0})
    (hb : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c R, (∀ k ∈ insert i S, z k ≠ 0) →
      |f z| ≤ K - ε * ∑ k ∈ insert i S, Real.log ‖z k‖) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) →
      |ReciprocityTheory.AnForm.A.poissonInt (fun ζ => f (Function.update z i ζ)) r (z i)| ≤
        K - ε * ∑ k ∈ S, Real.log ‖z k‖ := by
  intro ε hε
  obtain ⟨K, hK⟩ := hb ε hε
  refine ⟨K - ε * Real.log r, fun z hz hzS => ?_⟩
  set M := K - ε * Real.log r - ε * ∑ k ∈ S, Real.log ‖z k‖ with hM
  have hR : 0 < R := hr.trans hrR
  have hzc : dist z c < r := hz
  have hw : z i ∈ ball (0 : ℂ) r := by
    rw [mem_ball, ← hci]
    exact lt_of_le_of_lt (dist_le_pi_dist z c i) hzc
  have hupd : ∀ ζ ∈ sphere (0 : ℂ) r,
      Function.update z i ζ ∈ ball c R ∧ ∀ k ∈ insert i S, Function.update z i ζ k ≠ 0 := by
    intro ζ hζ
    have hζn : ‖ζ‖ = r := mem_sphere_zero_iff_norm.1 hζ
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_pi_lt_iff hR]
      intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, hci, dist_zero_right, hζn]
        exact hrR
      · rw [Function.update_of_ne hk]
        exact lt_of_le_of_lt (dist_le_pi_dist z c k) (hzc.trans hrR)
    · intro k hk
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self]
        intro h0
        rw [h0, norm_zero] at hζn
        exact hr.ne hζn
      · rw [Function.update_of_ne hki]
        exact hzS k ((Finset.mem_insert.1 hk).resolve_left hki)
  have hcont : ContinuousOn (fun ζ => f (Function.update z i ζ)) (sphere 0 r) := by
    refine hf.comp (f := fun ζ : ℂ => Function.update z i ζ)
      ((continuous_const (y := z)).update i continuous_id).continuousOn ?_
    intro ζ hζ
    exact hupd ζ hζ
  have hbd : ∀ ζ ∈ sphere (0 : ℂ) r, |f (Function.update z i ζ)| ≤ M := by
    intro ζ hζ
    have hζn : ‖ζ‖ = r := mem_sphere_zero_iff_norm.1 hζ
    obtain ⟨h1, h2⟩ := hupd ζ hζ
    have h3 := hK _ h1 h2
    rw [Finset.sum_insert hiS, Function.update_self, hζn] at h3
    have hs : ∑ k ∈ S, Real.log ‖Function.update z i ζ k‖ = ∑ k ∈ S, Real.log ‖z k‖ := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hki : k ≠ i := fun h => hiS (h ▸ hk)
      rw [Function.update_of_ne hki]
    rw [hs] at h3
    rw [hM]
    linarith
  have hP := ReciprocityTheory.AnForm.A.poissonKernel_zero_continuousOn hr hw
  set g : ℂ → ℝ := fun ζ => f (Function.update z i ζ) with hg
  have i3 : CircleIntegrable (|poissonKernel 0 (z i) • g|) 0 r :=
    ((hP.smul hcont).abs).circleIntegrable hr.le
  have i4 : CircleIntegrable (M • poissonKernel 0 (z i)) 0 r :=
    (hP.const_smul M).circleIntegrable hr.le
  have hpt : ∀ x ∈ sphere (0 : ℂ) |r|,
      (|poissonKernel 0 (z i) • g|) x ≤ (M • poissonKernel 0 (z i)) x := by
    intro x hx
    rw [abs_of_pos hr] at hx
    have hP0 := ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hw hx
    show |poissonKernel 0 (z i) x * g x| ≤ M * poissonKernel 0 (z i) x
    rw [abs_mul, abs_of_nonneg hP0]
    have := mul_le_mul_of_nonneg_left (hbd x hx) hP0
    linarith
  calc |ReciprocityTheory.AnForm.A.poissonInt g r (z i)|
      ≤ Real.circleAverage (|poissonKernel 0 (z i) • g|) 0 r :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (M • poissonKernel 0 (z i)) 0 r := Real.circleAverage_mono i3 i4 hpt
    _ = M := by
        rw [Real.circleAverage_smul, ReciprocityTheory.AnForm.A.circleAverage_poissonKernel_zero hw,
          smul_eq_mul, mul_one]
    _ = K - ε * Real.log r - ε * ∑ k ∈ S, Real.log ‖z k‖ := hM

end GlobalTheory
