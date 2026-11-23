import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_model_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧ (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u → (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) → u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) → ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧ ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left) (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u → w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u → (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ ν.φ)) := by
  first | exact @GlobalTheory.ModelFrameCompare.images_eigenBasis | exact GlobalTheory.ModelFrameCompare.images_eigenBasis | (intros; apply GlobalTheory.ModelFrameCompare.images_eigenBasis <;> assumption)
