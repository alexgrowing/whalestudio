import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjTwistedCentralizer
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariantStatement
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conj_twisted_centralizer : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
  (∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) →
  (∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂) →
  (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤) →
  ∃ ρ : GL (Fin n) ℂ → ℝ≥0∞, IsQuotNormaliser (twCent (thC n) d) μd ρ ∧
    ∀ (X : nilrad W₁ W₂) (g : GL (Fin n) ℂ), ρ (uOf X * g) = ρ g := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.tNormaliser | exact GlobalTheory.CompanionTheory.LocVan.tNormaliser | (intros; apply GlobalTheory.CompanionTheory.LocVan.tNormaliser <;> assumption)
