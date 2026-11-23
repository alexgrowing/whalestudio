import Mathlib
open Filter Topology

namespace GlobalTheory

theorem meromorphicAt_of_pow_mul_eq {f H : ℂ → ℂ} {s₁ : ℂ} {k : ℕ} {r : ℝ} (hr : 0 < r)
    (h : ∀ s ∈ Metric.ball s₁ r, s ≠ s₁ → H s = (s - s₁) ^ k * f s)
    (hH : DifferentiableOn ℂ H (Metric.ball s₁ r)) : MeromorphicAt f s₁ := by
  have hb : Metric.ball s₁ r ∈ 𝓝 s₁ := Metric.ball_mem_nhds _ hr
  have ha : AnalyticAt ℂ H s₁ := hH.analyticAt hb
  refine ⟨k + 1, ?_⟩
  have h1 : AnalyticAt ℂ (fun z => (z - s₁) * H z) s₁ :=
    (analyticAt_id.sub analyticAt_const).mul ha
  refine h1.congr ?_
  filter_upwards [hb] with z hz
  by_cases hzs : z = s₁
  · simp [hzs]
  · rw [h z hz hzs, smul_eq_mul]; ring

theorem eventually_eq_nhdsNE_of_meromorphic_of_eqOn_halfPlane : ∀ (f g : ℂ → ℂ) (σ₀ : ℝ),
    (∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → ℂ), 0 < r ∧ (∀ s ∈ Metric.ball s₁ r, s ≠ s₁ → H s = (s - s₁) ^ k * f s) ∧
      DifferentiableOn ℂ H (Metric.ball s₁ r)) →
    (∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → ℂ), 0 < r ∧ (∀ s ∈ Metric.ball s₁ r, s ≠ s₁ → H s = (s - s₁) ^ k * g s) ∧
      DifferentiableOn ℂ H (Metric.ball s₁ r)) →
    (∀ s : ℂ, σ₀ < s.re → f s = g s) → ∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, f t = g t := by
  intro f g σ₀ hf hg hfg s
  have hf' : ∀ x, MeromorphicAt f x := fun x => by
    obtain ⟨k, r, H, hr, h, hH⟩ := hf x
    exact meromorphicAt_of_pow_mul_eq hr h hH
  have hg' : ∀ x, MeromorphicAt g x := fun x => by
    obtain ⟨k, r, H, hr, h, hH⟩ := hg x
    exact meromorphicAt_of_pow_mul_eq hr h hH
  have hm : MeromorphicOn (f - g) Set.univ := fun x _ => (hf' x).sub (hg' x)
  by_contra hne
  have h1 : meromorphicOrderAt (f - g) s ≠ ⊤ := by
    intro h
    rw [meromorphicOrderAt_eq_top_iff] at h
    apply hne
    filter_upwards [h] with t ht
    exact sub_eq_zero.mp ht
  have h2 : meromorphicOrderAt (f - g) ((σ₀ + 1 : ℝ) : ℂ) ≠ ⊤ :=
    hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ s)
      (Set.mem_univ _) h1
  apply h2
  rw [meromorphicOrderAt_eq_top_iff]
  have ho : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {z : ℂ | σ₀ < z.re} ∈ 𝓝 ((σ₀ + 1 : ℝ) : ℂ) := ho.mem_nhds (by simp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hmem] with t ht
  exact sub_eq_zero.mpr (hfg t ht)

end GlobalTheory
