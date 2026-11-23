import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebra
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra : ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ), Continuous u → u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) → ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | exact GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | (intros; apply GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU <;> assumption)
