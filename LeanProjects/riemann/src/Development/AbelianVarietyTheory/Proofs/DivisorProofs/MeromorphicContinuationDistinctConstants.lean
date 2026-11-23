import Mathlib
open Filter Topology

theorem GlobalTheory.analytic_continuation_constant_term_projector : ∀ (Y : Type) (τ : Y → Y) (c₁ c₂ c₃ c₄ : ℂ → ℂ), Differentiable ℂ c₁ → Differentiable ℂ c₂ → Differentiable ℂ c₃ →
    Differentiable ℂ c₄ → ∀ (Ω Ω₁ : Set ℂ) (s₀ : ℂ), IsOpen Ω → IsPreconnected Ω → IsOpen Ω₁ → Ω₁.Nonempty → Ω₁ ⊆ Ω →
    s₀ ∈ Ω → c₁ s₀ ≠ c₂ s₀ → c₁ s₀ ≠ c₃ s₀ → c₁ s₀ ≠ c₄ s₀ → ∀ (Bf Fm : ℂ → Y → ℂ),
    (∀ y, ∀ s ∈ Ω, MeromorphicAt (Bf · y) s) → (∀ y, AnalyticAt ℂ (Bf · y) s₀) → (∀ y, DifferentiableOn ℂ (Fm · y) Ω) →
    (∀ s ∈ Ω₁, ∀ y, Fm s (τ y) = c₁ s * Fm s y) →
    (∀ s ∈ Ω₁, ∃ T₂ T₃ T₄ : Y → ℂ, (∀ y, Bf s y = Fm s y + T₂ y + T₃ y + T₄ y) ∧ (∀ y, T₂ (τ y) = c₂ s * T₂ y) ∧
      (∀ y, T₃ (τ y) = c₃ s * T₃ y) ∧ (∀ y, T₄ (τ y) = c₄ s * T₄ y)) →
    ∀ A Bb : Y → ℂ, (∀ y, Bf s₀ y = A y + Bb y) → (∀ y, A (τ y) = c₃ s₀ * A y) → (∀ y, Bb (τ y) = c₁ s₀ * Bb y) → Bb = Fm s₀ := by
  intro Y τ c₁ c₂ c₃ c₄ hc₁ hc₂ hc₃ hc₄ Ω Ω₁ s₀ hΩ hΩc hΩ₁ hne hsub hs₀ h12 h13 h14 Bf Fm hBm hBa hFd hFe
    hdec A Bb hAB hA hB

  let L : ℂ → (Y → ℂ) → (Y → ℂ) := fun c f y => f (τ y) - c * f y
  let P : ℂ → (Y → ℂ) → (Y → ℂ) := fun s f => L (c₂ s) (L (c₃ s) (L (c₄ s) f))
  let D : ℂ → ℂ := fun s => (c₁ s - c₂ s) * (c₁ s - c₃ s) * (c₁ s - c₄ s)
  have key : ∀ s ∈ Ω₁, ∀ y, P s (Bf s) y = D s * Fm s y := by
    intro s hs y
    obtain ⟨T₂, T₃, T₄, hd, h2, h3, h4⟩ := hdec s hs
    simp only [P, L, D, hd, h2, h3, h4, hFe s hs]
    ring
  have key₀ : ∀ y, P s₀ (Bf s₀) y = D s₀ * Bb y := by
    intro y
    simp only [P, L, D, hAB, hA, hB]
    ring
  have mL : ∀ (c : ℂ → ℂ), Differentiable ℂ c → ∀ (F : ℂ → Y → ℂ) (s : ℂ),
      (∀ y, MeromorphicAt (F · y) s) → ∀ y, MeromorphicAt (fun t => L (c t) (F t) y) s := by
    intro c hc F s hF y
    exact (hF (τ y)).sub ((hc.analyticAt s).meromorphicAt.mul (hF y))
  have aL : ∀ (c : ℂ → ℂ), Differentiable ℂ c → ∀ (F : ℂ → Y → ℂ) (s : ℂ),
      (∀ y, AnalyticAt ℂ (F · y) s) → ∀ y, AnalyticAt ℂ (fun t => L (c t) (F t) y) s := by
    intro c hc F s hF y
    exact (hF (τ y)).sub ((hc.analyticAt s).mul (hF y))
  have aD : ∀ s, AnalyticAt ℂ D s := by
    intro s
    exact (((hc₁.analyticAt s).sub (hc₂.analyticAt s)).mul ((hc₁.analyticAt s).sub (hc₃.analyticAt s))).mul
      ((hc₁.analyticAt s).sub (hc₄.analyticAt s))
  have aF : ∀ y, ∀ s ∈ Ω, AnalyticAt ℂ (Fm · y) s := fun y s hs =>
    (hFd y).analyticAt (hΩ.mem_nhds hs)
  funext y
  let H : ℂ → ℂ := fun s => P s (Bf s) y - D s * Fm s y
  have hHm : MeromorphicOn H Ω := by
    intro s hs
    have hB' : ∀ y, MeromorphicAt (Bf · y) s := fun y => hBm y s hs
    exact (mL c₂ hc₂ _ s (mL c₃ hc₃ _ s (mL c₄ hc₄ Bf s hB')) y).sub
      ((aD s).mul (aF y s hs)).meromorphicAt
  have hHa : AnalyticAt ℂ H s₀ :=
    (aL c₂ hc₂ _ s₀ (aL c₃ hc₃ _ s₀ (aL c₄ hc₄ Bf s₀ hBa)) y).sub ((aD s₀).mul (aF y s₀ hs₀))
  obtain ⟨x, hx⟩ := hne
  have htopx : meromorphicOrderAt H x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds (hΩ₁.mem_nhds hx)] with s hs
    simp only [H, key s hs, sub_self]
  have htop : meromorphicOrderAt H s₀ = ⊤ := by
    by_contra h
    exact hHm.meromorphicOrderAt_ne_top_of_isPreconnected hΩc hs₀ (hsub hx) h htopx
  rw [meromorphicOrderAt_eq_top_iff] at htop
  have hev : ∀ᶠ s in 𝓝 s₀, H s = 0 := hHa.frequently_zero_iff_eventually_zero.1 htop.frequently
  have h0 : H s₀ = 0 := hev.self_of_nhds
  have hD : D s₀ ≠ 0 := mul_ne_zero (mul_ne_zero (sub_ne_zero.2 h12) (sub_ne_zero.2 h13)) (sub_ne_zero.2 h14)
  have : D s₀ * Bb y = D s₀ * Fm s₀ y := by
    rw [← key₀ y]
    exact sub_eq_zero.1 h0
  exact mul_left_cancel₀ hD this
