import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMapCompatible
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
theorem _root_.GlobalTheory.T.tangent_basis_map_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (σ : E →+* ℂ) (U h : Fin (Dw.mult σ) → Fin g → A), IsUnit (pairDet h U) →
    ∀ (L : Type) [CommRing L] [Algebra c.F L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ z₀ : FrPt Xo c L, z₀.x = yL ≫ r ≫ pullback.fst _ _ →
    ∀ w : Fin (Dw.mult σ) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left),
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U i b)) (w i ≫ Y.m.φ)) →
      (∀ i, IsTanAtG Y.oF.t yL (w i)) → (∀ i, IsEigAt c σ (w i ≫ ν.φ)) →
      ∃ g₁ : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L, IsUnit g₁.det ∧
        ∀ i, IsCombAt z₀.x (z₀.u σ) (g₁ i) (w i ≫ ν.φ) := by
  first | exact @GlobalTheory.FrameCoordUnit.coord_unit | exact GlobalTheory.FrameCoordUnit.coord_unit | (intros; apply GlobalTheory.FrameCoordUnit.coord_unit <;> assumption)
