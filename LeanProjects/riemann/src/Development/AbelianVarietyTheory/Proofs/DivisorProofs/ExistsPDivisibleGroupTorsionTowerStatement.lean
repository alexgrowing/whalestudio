import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivisibleGroupTorsionTower
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
theorem _root_.GlobalTheory.T.exists_p_divisible_group_torsion_tower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (p : ℕ) [Fact p.Prime], IsProper t.G.hom → ∃ GG : PDivGroup p k, Nonempty (GG.TorsionTower t.G) := by
  first | exact @GlobalTheory.GroupBplus.Closed.exists_torsionTower | exact GlobalTheory.GroupBplus.Closed.exists_torsionTower | (intros; apply GlobalTheory.GroupBplus.Closed.exists_torsionTower <;> assumption)
