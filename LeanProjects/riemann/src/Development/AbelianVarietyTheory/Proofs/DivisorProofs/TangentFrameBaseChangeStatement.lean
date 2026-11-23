import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

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
theorem _root_.GlobalTheory.T.tangent_frame_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) {L k : Type}
    [CommRing L] [CommRing k] (φ : L →+* k) (yL : Sp L ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber L) ⟶ Y.t.G.left)) (cf : Fin g → L) (w : Sp (DualNumber L) ⟶ Y.oF.t.G.left)
    (w' : Sp (DualNumber k) ⟶ Y.oF.t.G.left),
    IsCombAtG Y.t (yL ≫ Y.j) e cf (w ≫ Y.m.φ) →
    IsCombAtG Y.t (spMap φ ≫ yL ≫ Y.j) (bcV Y.t φ e) (fun b => φ (cf b)) (w' ≫ Y.m.φ) →
    w' = spMap (dualMap φ) ≫ w := by
  first | exact @GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG | exact GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG | (intros; apply GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG <;> assumption)
