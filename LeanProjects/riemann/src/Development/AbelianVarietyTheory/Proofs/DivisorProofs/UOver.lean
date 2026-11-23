import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

def UAct {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R))
    (act : 𝓞 E → (P.A ⟶ P.A)) (σ : R →+* R') (u : Sp R' ⟶ Xo.XF c) : Prop :=
  ∃ (G : Over (Sp R')) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
    IsGrpPullback G P.A (spMap σ) α ∧ IsGrpPullback G Xo.univ.t.G (u ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∀ a, ∃ f : G ⟶ G, f.left ≫ α = α ≫ (act a).left ∧ f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left

theorem UAct.uOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R R' : Type} [CommRing R] [CommRing R'] {P : PolAV (Sp R)}
    {act : 𝓞 E → (P.A ⟶ P.A)} {σ : R →+* R'} {u : Sp R' ⟶ Xo.XF c} (h : UAct Xo c P act σ u) : UOver Xo c P σ u :=
  let ⟨G, i, α, β, h₁, h₂, h₃, _⟩ := h
  ⟨G, i, α, β, h₁, h₂, h₃⟩

end GlobalTheory.UCovSep
