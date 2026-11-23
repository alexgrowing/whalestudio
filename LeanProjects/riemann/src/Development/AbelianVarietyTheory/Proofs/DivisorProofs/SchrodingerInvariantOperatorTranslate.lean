import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

theorem commute_line_invariance {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] (P : V → V → ℝ) (hP : IsPairing P)
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) (u : V × V)
    (hT : ∀ (s : ℝ) (f g : 𝓢(V, ℂ)), ⇑g = schrF P (s • u) ⇑f → T g = T f)
    (w : V × V) (s : ℝ) (h h₁ g g₁ : 𝓢(V, ℂ)) (hh₁ : ⇑h₁ = schrF P (s • u) ⇑h)
    (hg : ⇑g = schrF P w ⇑h) (hg₁ : ⇑g₁ = schrF P w ⇑h₁) :
    T g₁ = Complex.exp (-(2 * Real.pi * Complex.I) * ((s * omega P w u : ℝ) : ℂ)) • T g := by
  set c := Complex.exp (-(2 * Real.pi * Complex.I) * ((s * omega P w u : ℝ) : ℂ)) with hcdef
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have pt : ∀ y, g₁ y = c * schrF P (s • u) (⇑g) y := by
    intro y
    rw [hg₁]
    simp only [schrF, hh₁, hg]
    rw [show y + w.1 + (s • u).1 = y + (s • u).1 + w.1 by abel]
    simp only [hcdef, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Prod.smul_fst, Prod.smul_snd, hP.addL, hP.smulL, hP.smulR, omega]
    push_cast
    ring
  have hk : ⇑(c⁻¹ • g₁) = schrF P (s • u) ⇑g := by
    funext y
    rw [SchwartzMap.smul_apply, pt y, smul_eq_mul, inv_mul_cancel_left₀ hc]
  have hT' := hT s g (c⁻¹ • g₁) hk
  have e : g₁ = c • (c⁻¹ • g₁) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [e, map_smul, hT']

theorem commute_line_invariance_target : ∀ {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) (u : V × V), (∀ (s : ℝ) (f g : 𝓢(V, ℂ)), ⇑g = GlobalTheory.ArchUniq.schrF P (s • u) ⇑f → T g = T f) → ∀ (w : V × V) (s : ℝ) (h h₁ g g₁ : 𝓢(V, ℂ)), ⇑h₁ = GlobalTheory.ArchUniq.schrF P (s • u) ⇑h → ⇑g = GlobalTheory.ArchUniq.schrF P w ⇑h → ⇑g₁ = GlobalTheory.ArchUniq.schrF P w ⇑h₁ → T g₁ = Complex.exp (-(2 * Real.pi * Complex.I) * ((s * GlobalTheory.ArchUniq.omega P w u : ℝ) : ℂ)) • T g :=
  fun P hP T u hT w s h h₁ g g₁ => commute_line_invariance P hP T u hT w s h h₁ g g₁

end GlobalTheory.ArchUniq
