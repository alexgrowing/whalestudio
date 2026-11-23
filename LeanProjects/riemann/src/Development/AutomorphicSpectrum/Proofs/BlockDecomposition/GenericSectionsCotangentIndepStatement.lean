import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndep
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
theorem _root_.GlobalTheory.T.generic_sections_cotangent_indep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep | exact GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep <;> assumption)
