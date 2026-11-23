import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ) (F : L2 (latticeGL E a) μ), F ∈ L2cusp μ → ∀ (t : ℝ) (x : GA E a), convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | exact GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul <;> assumption)
