import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleHeightEqSignatureDegree
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
theorem _root_.GlobalTheory.T.p_divisible_height_eq_signature_degree : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), GG.height = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.GroupBplus.Closed.height_eq_lattice_rank | exact GlobalTheory.GroupBplus.Closed.height_eq_lattice_rank | (intros; apply GlobalTheory.GroupBplus.Closed.height_eq_lattice_rank <;> assumption)
