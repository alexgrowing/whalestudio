import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPeriodRelation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_period_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers σ) xx := by
  first | exact @GlobalTheory.DetHT.ptAt_tangent_isEig | exact GlobalTheory.DetHT.ptAt_tangent_isEig | (intros; apply GlobalTheory.DetHT.ptAt_tangent_isEig <;> assumption)
