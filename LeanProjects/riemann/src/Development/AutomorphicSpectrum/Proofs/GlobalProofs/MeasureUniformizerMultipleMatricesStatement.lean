import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasureUniformizerMultipleMatrices
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_uniformizer_multiple_matrices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) = ENNReal.ofReal ((q : ℝ) ^ (-((n * m : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.CompanionTheory.QL.Vol.vol_IIset | exact GlobalTheory.CompanionTheory.QL.Vol.vol_IIset | (intros; apply GlobalTheory.CompanionTheory.QL.Vol.vol_IIset <;> assumption)
