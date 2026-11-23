import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantOperatorTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open scoped SchwartzMap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_invariant_operator_translate : ∀ {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) (u : V × V), (∀ (s : ℝ) (f g : 𝓢(V, ℂ)), ⇑g = GlobalTheory.ArchUniq.schrF P (s • u) ⇑f → T g = T f) → ∀ (w : V × V) (s : ℝ) (h h₁ g g₁ : 𝓢(V, ℂ)), ⇑h₁ = GlobalTheory.ArchUniq.schrF P (s • u) ⇑h → ⇑g = GlobalTheory.ArchUniq.schrF P w ⇑h → ⇑g₁ = GlobalTheory.ArchUniq.schrF P w ⇑h₁ → T g₁ = Complex.exp (-(2 * Real.pi * Complex.I) * ((s * GlobalTheory.ArchUniq.omega P w u : ℝ) : ℂ)) • T g := by
  first | exact @GlobalTheory.ArchUniq.commute_line_invariance_target | exact GlobalTheory.ArchUniq.commute_line_invariance_target | (intros; apply GlobalTheory.ArchUniq.commute_line_invariance_target <;> assumption)
