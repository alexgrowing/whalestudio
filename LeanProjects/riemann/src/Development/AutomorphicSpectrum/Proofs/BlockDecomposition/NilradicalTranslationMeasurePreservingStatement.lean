import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalTranslationMeasurePreserving
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_translation_measure_preserving : ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂),
  MeasurePreserving (nmul hW Y) ν ν := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving | exact GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving | (intros; apply GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving <;> assumption)
