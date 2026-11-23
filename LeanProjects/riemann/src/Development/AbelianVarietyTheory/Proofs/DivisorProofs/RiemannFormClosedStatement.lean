import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannFormClosed
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_closed : ∀ (n g : ℕ) (X : V n → Fl g) (α : V n → Alt n) (v : V n), ContDiffAt ℝ ∞ X v → (∀ᶠ u in 𝓝 v, IsType 1 1 (α u) ∧ ∀ ξ ζ : V n, eval₂ (α u) ξ ζ = (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.riem (fderiv ℝ X u ξ) (fderiv ℝ X u ζ) : ℝ)) → delAt α v = 0 ∧ dbarAt α v = 0 := by
  first | exact @GlobalTheory.FlatClosed.closed_of_eq_riem | exact GlobalTheory.FlatClosed.closed_of_eq_riem | (intros; apply GlobalTheory.FlatClosed.closed_of_eq_riem <;> assumption)
