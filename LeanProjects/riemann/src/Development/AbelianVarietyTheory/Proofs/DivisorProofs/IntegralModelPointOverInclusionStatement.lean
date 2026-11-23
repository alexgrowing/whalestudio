import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPointOverInclusion
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
theorem _root_.GlobalTheory.T.integral_model_point_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L), (yL ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c L ∧
      (∀ z : FrPt Xo c L, z.x = yL ≫ r ≫ pullback.fst _ _ → ptF z = yL ≫ r) ∧
      ∀ (σ : E →+* ℂ) (a : 𝓞 E), algebraMap c.F L (embK c σ a) = io (β (embV c' W σ a)) := by
  first | exact @GlobalTheory.GenChartAlg.exists_algebra_of_genPt | exact GlobalTheory.GenChartAlg.exists_algebra_of_genPt | (intros; apply GlobalTheory.GenChartAlg.exists_algebra_of_genPt <;> assumption)
