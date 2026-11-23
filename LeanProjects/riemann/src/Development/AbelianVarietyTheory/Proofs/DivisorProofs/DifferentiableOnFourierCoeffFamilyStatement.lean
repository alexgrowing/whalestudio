import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFourierCoeffFamily
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_fourier_coeff_family : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} (a : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ a (cov U g) → ∀ n : Fin g → ℤ, DifferentiableOn ℂ (fun b => cf (fun z => a (b, z)) n) U := by
  first | exact @GlobalTheory.differentiableOn_cf_fibre_of_holomorphic | exact GlobalTheory.differentiableOn_cf_fibre_of_holomorphic | (intros; apply GlobalTheory.differentiableOn_cf_fibre_of_holomorphic <;> assumption)
