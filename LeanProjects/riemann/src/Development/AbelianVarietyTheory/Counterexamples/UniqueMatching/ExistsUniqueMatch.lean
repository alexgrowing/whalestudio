import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArcPtX
import Formalism.LocalToGlobal.ProjectiveLattices.LieRel
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.ArcTieProbe

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem mono_j (Y : Model Xo c β) [Mono (spMap β)] : Mono Y.j := by
  have := Y.jQ_open
  unfold Model.j
  infer_instance

section Comparison₂

variable (Y : Model Xo c β) {S R : Scheme.{0}} {i : S ⟶ R} {χ : R ⟶ Y.X} {t : SAB H R} (m : SABMap t Y.t χ)
  {t' : SAB H S}

def Tied {x : S ⟶ Xo.X} (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' t i) : Prop :=
  ∃ g : t'.G.left ⟶ Y.oF.t.G.left, g ≫ Y.m0.toSABMap.φ = m1.φ ∧ g ≫ Y.m.φ = m2.φ ≫ m.φ

end Comparison₂

variable (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁}
  (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
  (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
  [Algebra c.F (ArcS Dw K₁)]

end GlobalTheory.ArcTieProbe
