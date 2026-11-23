import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotient
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_section_quotient : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G] (H : Subgroup G), IsClosed (H : Set G) → ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  first | exact @GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | exact GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | (intros; apply GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section <;> assumption)
