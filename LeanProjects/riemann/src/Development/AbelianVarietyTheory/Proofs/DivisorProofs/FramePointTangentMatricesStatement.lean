import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointTangentMatrices
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
theorem _root_.GlobalTheory.T.frame_point_tangent_matrices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (L : Type) [CommRing L] [Algebra c.F L] (z₀ : FrPt Xo c L)
    (τ : Psi H) (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) L)
    (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) L)
    (v₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left))
    (v₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left)),
    IsUnit g₁.det → IsUnit g₂.det → (∀ i, IsCombAt z₀.x (z₀.u τ.1) (g₁ i) (v₁ i)) →
    (∀ i, IsCombAt z₀.x (z₀.u (conjEmb τ.1)) (g₂ i) (v₂ i)) →
    ∃ z : FrPt Xo c L, z.x = z₀.x ∧ (∀ i, z.u τ.1 i = v₁ i) ∧ ∀ i, z.u (conjEmb τ.1) i = v₂ i := by
  first | exact @GlobalTheory.FrameChangePair.exists_frPt_comb_pair | exact GlobalTheory.FrameChangePair.exists_frPt_comb_pair | (intros; apply GlobalTheory.FrameChangePair.exists_frPt_comb_pair <;> assumption)
