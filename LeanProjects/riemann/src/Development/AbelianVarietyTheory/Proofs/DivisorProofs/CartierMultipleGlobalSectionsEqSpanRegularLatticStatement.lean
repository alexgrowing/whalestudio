import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLattic
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  first | exact @GlobalTheory.Desc.sec_eq_spanBy_N | exact GlobalTheory.Desc.sec_eq_spanBy_N | (intros; apply GlobalTheory.Desc.sec_eq_spanBy_N <;> assumption)
