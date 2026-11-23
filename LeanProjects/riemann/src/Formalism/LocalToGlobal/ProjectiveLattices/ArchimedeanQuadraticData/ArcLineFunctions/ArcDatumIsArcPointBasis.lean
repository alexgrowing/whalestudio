import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.FunDef
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc

noncomputable section

namespace Formalism.L2.Pj.QAt

open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

variable {D : D7} {T : Core D}

structure ArcDatumAt (T : Core D) (j : ℕ) (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] where

  Wp : ValuationSubring ℂ
  Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype
  a : ArcIn (T.Q.Dw j) T.Q.l (RingHom.id T.Q.c.F) K₁ (algebraMap T.Q.c.F K₁)
  χ : Sp (PowerSeries K₁) ⟶ Y.X

  chiOver : χ ≫ Y.s = spMap ((PowerSeries.C (R := K₁)).comp
    ((algebraMap T.Q.c.F K₁).comp (T.Q.c.V Wp).subtype))
  W : ArcWit Y (a.restrict (T.Q.c.V Wp).subtype) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁))
    PowerSeries.X χ
  e : ∀ τ, Fin ((T.Q.Dw j).mult τ) →
    ReciprocityTheory.ChartRestriction.G.Out.GtPt (a.restrict (T.Q.c.V Wp).subtype).D₀ (epsR K₁)
  yF : FrPt (T.Q.Xo j) T.Q.c (ArcS (T.Q.Dw j) K₁)

  th : (a.restrict (T.Q.c.V Wp).subtype).D₀.P.L.Sec
  arcDatum_isArc_point_basis : IsArcPointPowerSeries Y (a.restrict (T.Q.c.V Wp).subtype) χ W e yF
  isArc3 : IsArcPt3At Y (a.restrict (T.Q.c.V Wp).subtype) χ W yF th
  μ : ArcLt (T.Q.Dw j) →₀ ℕ
  jj : ℤ

theorem ArcDatumAt.isArc {T : Core D} {j : ℕ} {K₁ : Type} [Field K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] (d : ArcDatumAt T j K₁) :
    IsArcPt d.Y (d.a.restrict (T.Q.c.V d.Wp).subtype) d.χ d.W d.e d.yF :=
  ⟨d.arcDatum_isArc_point_basis, d.th, d.isArc3⟩

end Formalism.L2.Pj.QAt
