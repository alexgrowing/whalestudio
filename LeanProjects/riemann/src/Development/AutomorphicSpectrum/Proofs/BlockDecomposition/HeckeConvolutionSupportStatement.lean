import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_convolution_support : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
  IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧ ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | exact GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | (intros; apply GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke <;> assumption)
