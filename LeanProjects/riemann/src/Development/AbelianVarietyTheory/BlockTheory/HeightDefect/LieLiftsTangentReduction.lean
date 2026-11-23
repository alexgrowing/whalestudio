import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj

abbrev epsRed (R : Type) [CommRing R] : Sp R ⟶ Sp (DualNumber R) :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom

def IsGtTangent {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (ν : GtPt D (epsR R)) : Prop :=
  epsRed R ≫ ν.b.left = eSec D.P.A ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (ν.s χ) (epsRed R)) (LB.oneGen D.P.L)

theorem IsGtTangent.isTangent {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ν : GtPt D (epsR R)}
    (h : IsGtTangent ν) : IsTangent ν.b := h.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def LieLifts {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
    {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ) : Prop :=
  ∀ ν : GtPt a.D₀ (epsR K₁), IsGtTangent ν →
    ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsTangent v ∧ IsLieImage W ν v

variable (Xo c) in

def ArcLieLift : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K₁ : Type) [Field K₁] (b : O →+* K₁)
    (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ), LieLifts W

end GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
