import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjCompactOfDiagonalNilradical
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_compact_of_diagonal_nilradical : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
  (P : GL (Fin n) ℂ), W₁ ≤ W₂ →
  (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) →
  (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) →
  ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.Slice.slice_measure_ne_top | exact GlobalTheory.CompanionTheory.LocVan.Slice.slice_measure_ne_top | (intros; apply GlobalTheory.CompanionTheory.LocVan.Slice.slice_measure_ne_top <;> assumption)
