import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def GtTan {K₁ : Type} [Field K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) : Prop :=
  ∃ g₀ : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (Over.mk (𝟙 (Sp K₁))), g₀.IsZero ∧
    ReciprocityTheory.ChartRestriction.G.Out.GtPt.IsPull (spMap (TrivSqZeroExt.fstHom K₁ K₁ K₁).toRingHom) ν g₀

def LieArcSt (Y : Model Xo c β) : Prop :=
  ∀ {K₁ : Type} [Field K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)), GtTan ν →
    ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsLieImage W ν v

end Formalism.L2.Pj
