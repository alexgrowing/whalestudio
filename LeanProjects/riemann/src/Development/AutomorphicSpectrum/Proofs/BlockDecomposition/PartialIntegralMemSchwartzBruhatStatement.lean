import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhat
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_integral_mem_schwartzBruhat : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B), (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  first | exact @GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | exact GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | (intros; apply GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB <;> assumption)
