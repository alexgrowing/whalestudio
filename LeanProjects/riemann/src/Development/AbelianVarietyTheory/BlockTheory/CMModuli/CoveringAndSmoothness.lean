import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsUnifBase (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) : Prop :=
  CharZero R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    (ξ ⁻¹' abLocus Y.t.G).Nonempty ∧
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ) (S : SplitExt (Sp (IsLocalRing.ResidueField R))),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)

def CovAt (Y : Model Xo c β) (p : ℕ) (x : Y.X) : Prop :=
  ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsLocalRing (R i))
    (ξ : ∀ i, Sp (R i) ⟶ Y.X),
    (∀ i, IsUnifBase Y (R i) (ξ i) ∧ ξ i (IsLocalRing.closedPoint (R i)) = x) ∧
    ∀ (C V : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [CommRing V] [IsLocalRing V] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 →
      ∀ y : Sp V ⟶ Y.X, y (IsLocalRing.closedPoint V) = x →
        Set.range (spMap (algebraMap V C) ≫ y) ⊆ abLocus Y.t.G →
        ∃ (i : Fin n) (φ : R i →+* V), IsLocalHom φ ∧ spMap φ ≫ ξ i = y

def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)

theorem IsUnifBase.out {Y : Model Xo c β} (h3 : Y.N3) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsUnifBase Y R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by
  obtain ⟨h0, hn, hi, hc, hU, t, m, S, hS⟩ := h
  exact ⟨t, m, h3 R hn hi hc ξ t m hU ⟨S, hS⟩⟩

theorem AbLocusSmooth.smooth {Y : Model Xo c β} (h : AbLocusSmooth Y) (U : Y.X.Opens)
    (hU : (U : Set Y.X) = abLocus Y.t.G) : SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s) := by
  obtain ⟨U', hU', hs⟩ := h
  obtain rfl : U = U' := SetLike.coe_injective (hU.trans hU'.symm)
  exact hs

end One

def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'

def CoveringLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ (i : Idx H p) (x : (Y i).X), CovAt (Y i) p x

def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)

def CoveringAndSmoothness : Prop := CoveringLemma ∧ SmoothnessLemma

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
