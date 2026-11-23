import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRadialPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

theorem RadialPrimitive.primitive_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by
  have hd : deriv (fun t => ∫ τ in c..t, f τ) = f :=
    funext fun t => hf.continuous.deriv_integral f c t
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => ?_, by rw [hd]; exact hf⟩, hd⟩
  exact (hf.continuous.integral_hasStrictDerivAt c t).hasDerivAt.differentiableAt

theorem RadialPrimitive.proof : RadialPrimitive.Statement := by
  intro e a t₀ T ha ht₀ hconst hzero hint
  set c : ℝ := ((e + 1 : ℕ) : ℝ) with hc
  set g : ℝ → ℝ := fun τ => a τ * (c * τ ^ (e + 1 - 1)) with hg
  set P : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, g τ with hP
  have hgs : ContDiff ℝ ∞ g := ha.mul (contDiff_const.mul (contDiff_id.pow _))
  obtain ⟨hPs, hPd⟩ := RadialPrimitive.primitive_contDiff g hgs 0
  have hrt : ∀ t, radialTransform (e + 1) a t = a t * t ^ (e + 1) - P t := fun t => rfl

  have hPc : ∀ t ∈ Set.Icc 0 t₀, P t = a 0 * t ^ (e + 1) := by
    intro t ht
    have h0 := radialTransform_eq_zero_of_const e a hconst ht
    rw [hrt, hconst t ht] at h0
    linarith
  set h : ℝ → ℝ := fun t => if t < t₀ then a 0 else P t / t ^ (e + 1) with hh
  have hlow : ∀ t, t < t₀ → h t = a 0 := fun t ht => if_pos ht
  have hpos : ∀ t, 0 < t → h t = P t / t ^ (e + 1) := by
    intro t ht
    by_cases h1 : t < t₀
    · rw [hlow t h1, hPc t ⟨ht.le, h1.le⟩, mul_div_assoc, div_self (pow_ne_zero _ ht.ne'), mul_one]
    · exact if_neg h1
  have hlowE : ∀ x, x < t₀ → h =ᶠ[nhds x] fun _ => a 0 := fun x hx =>
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) fun t ht => hlow t ht
  have hposE : ∀ x, 0 < x → h =ᶠ[nhds x] fun t => P t / t ^ (e + 1) := fun x hx =>
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun t ht => hpos t ht
  have hs : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < t₀
    · exact contDiffAt_const.congr_of_eventuallyEq (hlowE x hx)
    · have hx0 : 0 < x := lt_of_lt_of_le ht₀ (not_lt.1 hx)
      exact (hPs.contDiffAt.div (contDiff_id.pow _).contDiffAt (pow_ne_zero _ hx0.ne')).congr_of_eventuallyEq
        (hposE x hx0)

  set R : ℝ := max T t₀ with hR
  have hPz : ∀ t, R ≤ t → P t = 0 := by
    intro t ht
    have hTt : T ≤ t := le_trans (le_max_left _ _) ht
    have hgc : Continuous g := hgs.continuous
    have htail : ∫ τ in T..t, g τ = 0 := by
      have hcg : ∫ τ in T..t, g τ = ∫ τ in T..t, (0 : ℝ) :=
        intervalIntegral.integral_congr fun τ hτ => by
          rw [Set.uIcc_of_le hTt] at hτ
          simp [hg, hzero τ hτ.1]
      rw [hcg]
      simp
    have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := T) (c := t)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    simp only [hP]
    rw [← this, htail, add_zero]
    exact hint
  have hhz : ∀ t, R ≤ t → h t = 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₀ (le_trans (le_max_right _ _) ht)
    rw [hpos t ht0, hPz t ht, zero_div]
  obtain ⟨hQs, hQd⟩ := RadialPrimitive.primitive_contDiff h hs R
  refine ⟨fun t => ∫ τ in R..t, h τ, hQs, ⟨R, fun t ht => ?_⟩, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · have hcg : ∫ τ in R..t, h τ = ∫ τ in R..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [Set.uIcc_of_le ht] at hτ
        exact hhz τ hτ.1
    show ∫ τ in R..t, h τ = 0
    rw [hcg]
    simp
  · rw [hQd]
    exact hlow 0 ht₀
  · rw [hQd, (hlowE 0 ht₀).deriv_eq]
    simp
  · rw [hQd, hpos t ht, hrt, div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')]
    ring
  · rw [hQd, (hposE t ht).deriv_eq, hrt]
    have hPt : HasDerivAt P (g t) t := (hgs.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hq : HasDerivAt (fun s => P s / s ^ (e + 1))
        ((g t * t ^ (e + 1) - P t * (((e + 1 : ℕ) : ℝ) * t ^ (e + 1 - 1))) / (t ^ (e + 1)) ^ 2) t :=
      hPt.div (hasDerivAt_pow (e + 1) t) (pow_ne_zero _ ht.ne')
    rw [hq.deriv]
    simp only [hg, hc, Nat.add_sub_cancel]
    have ht' : t ≠ 0 := ht.ne'
    push_cast
    field_simp
    ring

end

end GroundTheory.Heights₂.Heights
