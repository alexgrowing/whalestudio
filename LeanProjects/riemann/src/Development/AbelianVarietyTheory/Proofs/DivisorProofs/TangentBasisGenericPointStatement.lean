import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisGenericPoint
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
theorem _root_.GlobalTheory.T.tangent_basis_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ cf : Fin g → L, ∃ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left,
      IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf (w ≫ Y.m.φ) ∧ IsTanAtG Y.oF.t yL w := by
  first | exact @GlobalTheory.FlatModel.LiftGen.exists_lift_comb | exact GlobalTheory.FlatModel.LiftGen.exists_lift_comb | (intros; apply GlobalTheory.FlatModel.LiftGen.exists_lift_comb <;> assumption)
