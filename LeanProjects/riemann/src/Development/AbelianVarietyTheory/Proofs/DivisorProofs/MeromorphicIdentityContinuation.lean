import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem meromorphicAt_of_localForm {f : ℂ → ℂ} {s₀ : ℂ}
    (h : ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → ℂ), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → Hol s = (s - s₀) ^ k * f s) ∧
      DifferentiableOn ℂ Hol U) : MeromorphicAt f s₀ := by
  obtain ⟨k, U, Hol, hU, hEq, hD⟩ := h
  have hA : AnalyticAt ℂ Hol s₀ := hD.analyticAt hU
  have hM : MeromorphicAt (fun s => (s - s₀) ^ (-(k : ℤ)) • Hol s) s₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow (-(k : ℤ))).smul hA.meromorphicAt
  refine hM.congr ?_
  have hU' : U ∈ 𝓝[≠] s₀ := nhdsWithin_le_nhds hU
  have : ∀ᶠ s in 𝓝[≠] s₀, s ∈ U ∧ s ≠ s₀ :=
    Filter.Eventually.and hU' self_mem_nhdsWithin
  filter_upwards [this] with s ⟨hsU, hne⟩
  have hne' : (s - s₀) ≠ 0 := sub_ne_zero.mpr hne
  simp only [smul_eq_mul, hEq s hsU hne, zpow_neg, zpow_natCast]
  field_simp

theorem identity_of_localForm_halfPlane : ∀ (f₁ f₂ : ℂ → ℂ) (c : ℝ),
    (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → ℂ), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → Hol s = (s - s₀) ^ k * f₁ s) ∧
      DifferentiableOn ℂ Hol U) →
    (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → ℂ), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → Hol s = (s - s₀) ^ k * f₂ s) ∧
      DifferentiableOn ℂ Hol U) →
    (∀ s : ℂ, c < s.re → f₁ s = f₂ s) → ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, f₁ s = f₂ s := by
  intro f₁ f₂ c h₁ h₂ hc s₀
  have hM : MeromorphicOn (f₁ - f₂) Set.univ := fun z _ =>
    (meromorphicAt_of_localForm (h₁ z)).sub (meromorphicAt_of_localForm (h₂ z))
  set y : ℂ := ((c + 1 : ℝ) : ℂ)
  have hy : meromorphicOrderAt (f₁ - f₂) y = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hopen : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : y ∈ {s : ℂ | c < s.re} := by simp [y]
    have hN : {s : ℂ | c < s.re} ∈ 𝓝[≠] y := nhdsWithin_le_nhds (hopen.mem_nhds hmem)
    filter_upwards [hN] with s hs
    simp [hc s hs]
  have hs₀ : meromorphicOrderAt (f₁ - f₂) s₀ = ⊤ := by
    by_contra hne
    exact hM.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ s₀)
      (Set.mem_univ y) hne hy
  rw [meromorphicOrderAt_eq_top_iff] at hs₀
  filter_upwards [hs₀] with s hs
  simpa [sub_eq_zero] using hs

end GlobalTheory
