import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointModelAbelianMap
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
theorem _root_.GlobalTheory.T.padic_point_model_abelian_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (y : FrPt Xo c ℂ_[p]), GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left, w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy →
    spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left →
    ∀ σ : E →+* ℂ, (∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ) →
    IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  first | exact @GlobalTheory.FlatModel.tanEig_of_model | exact GlobalTheory.FlatModel.tanEig_of_model | (intros; apply GlobalTheory.FlatModel.tanEig_of_model <;> assumption)
