import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAtHeightOneVerticalPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_at_height_one_vertical_point : ∀ (σ : Setup) (p : Sp σ.R) (z : (σ.C p).G.left), p.asIdeal.height = 1 → Vert (σ.C p).G.hom (σ.ρ p σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C p).G.hom) (maximalIdeal (σ.C p).R) (σ.θ p) (σ.W p) (regSet z) := by
  first | exact @GlobalTheory.Desc.gaussAt_chart_of_height_one | exact GlobalTheory.Desc.gaussAt_chart_of_height_one | (intros; apply GlobalTheory.Desc.gaussAt_chart_of_height_one <;> assumption)
