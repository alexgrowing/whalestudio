import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalks
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
theorem _root_.GlobalTheory.T.hyperplane_cut_good_stalks : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) (F : X.Modules) [IsFiniteQC F] {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec), GoodStalks F (Fin.cons s t : Fin (d + 1) → L.Sec) → Mono (cutHom F hL s) ∧ GoodStalks (cut F hL s) t := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut | exact GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut <;> assumption)
