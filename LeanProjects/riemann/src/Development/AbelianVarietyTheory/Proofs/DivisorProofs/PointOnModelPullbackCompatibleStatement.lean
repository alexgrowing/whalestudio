import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_on_model_pullback_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (X : LieG P.Gt) (u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), ITie P π X u0 →
    ∃ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left,
      w ≫ Y.m.φ = spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ u0 ∧
      w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy ∧
      spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left ∧
      LieTie P ψ X w := by
  first | exact @GlobalTheory.FlatModel.LiftW.liftW | exact GlobalTheory.FlatModel.LiftW.liftW | (intros; apply GlobalTheory.FlatModel.LiftW.liftW <;> assumption)
