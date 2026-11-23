import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_polynomial : ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ, ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial | exact GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial | (intros; apply GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial <;> assumption)
