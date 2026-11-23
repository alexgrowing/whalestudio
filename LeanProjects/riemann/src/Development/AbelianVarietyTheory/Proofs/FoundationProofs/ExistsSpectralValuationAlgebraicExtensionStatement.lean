import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtension
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectral_valuation_algebraic_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ), IsNonarchimedean f → f.IsNontrivial → CompleteSpace (WithAbs f) → ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧ ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  first | exact @GlobalTheory.exists_spectralValuation | exact GlobalTheory.exists_spectralValuation | (intros; apply GlobalTheory.exists_spectralValuation <;> assumption)
