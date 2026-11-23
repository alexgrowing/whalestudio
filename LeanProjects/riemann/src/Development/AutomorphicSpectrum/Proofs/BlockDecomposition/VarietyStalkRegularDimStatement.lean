import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDim
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.variety_stalk_regular_dim : ∀ (Y : Var ℂ) (x : Y.X), IsRegularLocalRing (Y.X.presheaf.stalk x) ∧ ringKrullDim (Y.X.presheaf.stalk x) ≤ Y.dim := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le | exact GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le <;> assumption)
