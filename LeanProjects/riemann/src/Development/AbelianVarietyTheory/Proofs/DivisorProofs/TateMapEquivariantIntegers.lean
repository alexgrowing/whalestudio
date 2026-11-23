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

namespace GlobalTheory.GroupBplus.Closed

theorem tau_smul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ (a : 𝓞 E) (x : Dw.La), tau tw I (a • x) = tateMap GG GG k (tw.act t.act a) (tau tw I x) := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I a x
  haveI := t.act.hom a
  refine TateOver.ext (funext fun n => ?_)
  refine tw.inj n k _ _ ?_
  change spOver (latPt tw I n (a • x)) ≫ tw.y n =
    spOver ((latPt tw I n x).comp ((tw.act t.act a).app n : GG.A n →ₐ[k] GG.A n)) ≫ tw.y n
  rw [latPt_y, I.lin, ← spOver_comp, Category.assoc, tw.act_apply, tw.map_y]
  simp only [← Category.assoc, latPt_y]

end GlobalTheory.GroupBplus.Closed
