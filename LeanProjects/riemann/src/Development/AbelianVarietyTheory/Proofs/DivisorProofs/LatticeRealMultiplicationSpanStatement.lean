import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRealMultiplicationSpan
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
open NumberField GlobalTheory.RealMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_real_multiplication_span : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ → (∀ j, 0 < h j) →
    ∀ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) → (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') →
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') →
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) →
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) →
    (∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ Λ) →
    ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} := by
  first | exact @GlobalTheory.RealMult.SpanDual.dualLat_le_span_values | exact GlobalTheory.RealMult.SpanDual.dualLat_le_span_values | (intros; apply GlobalTheory.RealMult.SpanDual.dualLat_le_span_values <;> assumption)
