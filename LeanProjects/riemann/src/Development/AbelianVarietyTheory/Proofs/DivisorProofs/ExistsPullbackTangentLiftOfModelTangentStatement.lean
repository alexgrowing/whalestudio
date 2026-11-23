import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTangentLiftOfModelTangent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_tangent_lift_of_modelTangent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), ∃ w : epsOver V V ⟶ G.G, IsTan w ∧ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  first | exact @GlobalTheory.TanLiftPull.exists_isTan_lift | exact GlobalTheory.TanLiftPull.exists_isTan_lift | (intros; apply GlobalTheory.TanLiftPull.exists_isTan_lift <;> assumption)
