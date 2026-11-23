import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibility
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
theorem _root_.GlobalTheory.T.embedding_section_compatibility : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (L : Type) [CommRing L] [Algebra c.F L]
    (yL : Sp L ⟶ Xo'.XF c') (σ : E →+* ℂ) (s : 𝓞 E →+* L), (∀ a, algebraMap c.F L (embK c σ a) = s a) →
    ∀ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left, IsTanAtG Y.oF.t yL w → IsEigG Y.t s (w ≫ Y.m.φ) →
      IsTanAt (yL ≫ r ≫ pullback.fst _ _) (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  first | exact @GlobalTheory.FlatModel.tan_eig_push | exact GlobalTheory.FlatModel.tan_eig_push | (intros; apply GlobalTheory.FlatModel.tan_eig_push <;> assumption)
