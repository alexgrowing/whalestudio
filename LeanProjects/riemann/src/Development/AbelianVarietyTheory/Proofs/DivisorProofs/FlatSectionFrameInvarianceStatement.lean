import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
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
theorem _root_.GlobalTheory.T.flat_section_frame_invariance : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) →
    ∀ {k : Type} [Field k] [Algebra c.F k] (z y : FrPt Xo c k), z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) k),
      (∀ i, IsCombAt y.x (y.u τ.1) (g₁ i) (z.u τ.1 i)) →
      (∀ i, IsCombAt y.x (y.u (conjEmb τ.1)) (g₂ i) (z.u (conjEmb τ.1) i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y := by
  first | exact @GlobalTheory.FlatGL.evR_flat_chg | exact GlobalTheory.FlatGL.evR_flat_chg | (intros; apply GlobalTheory.FlatGL.evR_flat_chg <;> assumption)
