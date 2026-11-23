import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightNilradicalIntegralOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariantStatement
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_nilradical_integral_one : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  (∀ Y : nilrad W₁ W₂, MeasurePreserving (nmul hW Y) ν ν) →
  ∃ w : GL (Fin n) ℂ → ℝ≥0∞, Measurable w ∧
    ∀ g : GL (Fin n) ℂ, ∫⁻ X, w ((uOf X)⁻¹ * g) ∂ν = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser | exact GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser | (intros; apply GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser <;> assumption)
