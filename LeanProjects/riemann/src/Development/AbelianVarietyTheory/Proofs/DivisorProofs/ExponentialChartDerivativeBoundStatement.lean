import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialChartDerivativeBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_chart_derivative_bound : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g), IsExpChart e ex → ∀ y₀ ∈ e.source, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (v : TanM (y.1 ≫ genι s.T.Z) s.T.Z.t.G) (w : Fin g → ℂ), IsDerivAt0 (fun u => (ex y u).left) w (tv v).left → ‖w‖ ^ 2 ≤ C * (x.met σ y v v).re := by
  first | exact @GlobalTheory.ExpChartMetric.exp_coord_sq_le_met | exact GlobalTheory.ExpChartMetric.exp_coord_sq_le_met | (intros; apply GlobalTheory.ExpChartMetric.exp_coord_sq_le_met <;> assumption)
