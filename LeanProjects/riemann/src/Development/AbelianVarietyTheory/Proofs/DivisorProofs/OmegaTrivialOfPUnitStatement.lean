import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaTrivialOfPUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_trivial_of_p_unit : ∀ {O : Type} [CommRing O] {p : ℕ} [Fact p.Prime] {A : Over (Sp O)} [GrpObj A] {G : PDivGroup p O} (θ : TorsionMap A G), IsUnit (p : O) → Subsingleton G.omega ∧ θ.IsOmega 0 := by
  first | exact @GlobalTheory.GroupBplus.Closed.isOmega_zero_of_isUnit | exact GlobalTheory.GroupBplus.Closed.isOmega_zero_of_isUnit | (intros; apply GlobalTheory.GroupBplus.Closed.isOmega_zero_of_isUnit <;> assumption)
