import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebr
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra : ∀ (B : RowsAut) (A : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (χ : B.I.Gf → ℂ) (ψ : B.I.GA → ℂ) (E : gInf B), ContDiff ℝ ∞ A → HasCompactSupport A → Continuous χ → HasCompactSupport χ → (∀ y, ψ y = A (fun v i j => uMat (y.1 v) i j) * χ y.2) → Continuous ψ ∧ HasCompactSupport ψ ∧ ∃ ψ' : B.I.GA → ℂ, Continuous ψ' ∧ HasCompactSupport ψ' ∧ ∀ F : B.I.L2 B.μf B.fund, HasDerivAt (fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf))) (∫ y, ψ' y • B.R y F ∂(B.I.muA B.μf)) 0 ∧ ∀ x : B.I.GA, HasDerivAt (fun t : ℝ => ∫ z, ψ ((x * ((fun v => expU (t • E v)), 1))⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) (∫ z, ψ' (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) 0 := by
  first | exact @GlobalTheory.ConvDeriv.convolution_hasDerivAt | exact GlobalTheory.ConvDeriv.convolution_hasDerivAt | (intros; apply GlobalTheory.ConvDeriv.convolution_hasDerivAt <;> assumption)
