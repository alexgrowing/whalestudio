import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsChartEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_chart_eq_span : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ), Sec (σ.D₁ x) k = spanBy (GlobalTheory.Desc.cst (σ.C x).G.hom) (σ.θ x '' σ.N k) := by
  first | exact @GlobalTheory.Desc.ChartSpan.sec_eq_spanBy | exact GlobalTheory.Desc.ChartSpan.sec_eq_spanBy | (intros; apply GlobalTheory.Desc.ChartSpan.sec_eq_spanBy <;> assumption)
