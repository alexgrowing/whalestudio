import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateMapEquivariantIntegers
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
theorem _root_.GlobalTheory.T.tate_map_equivariant_integers : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ (a : 𝓞 E) (x : Dw.La), tau tw I (a • x) = tateMap GG GG k (tw.act t.act a) (tau tw I x) := by
  first | exact @GlobalTheory.GroupBplus.Closed.tau_smul | exact GlobalTheory.GroupBplus.Closed.tau_smul | (intros; apply GlobalTheory.GroupBplus.Closed.tau_smul <;> assumption)
