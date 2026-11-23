import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicVectorIntegralProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_vector_integral_product : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ), ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) = (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.Split.integral_split | exact GlobalTheory.CompanionTheory.CutOff.Split.integral_split | (intros; apply GlobalTheory.CompanionTheory.CutOff.Split.integral_split <;> assumption)
