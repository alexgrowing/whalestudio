import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section OneModel

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsChartAt (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) :
    Prop :=
  CharZero R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    ξ (IsLocalRing.closedPoint R) = x ∧ (ξ ⁻¹' abLocus Y.t.G).Nonempty ∧
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ) (S : SplitExt (Sp (IsLocalRing.ResidueField R))),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)

def CoveredByCharts (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ x : Y.X, ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDomain (R i))
    (_ : ∀ i, IsLocalRing (R i)) (ξ : ∀ i, Sp (R i) ⟶ Y.X),
    (∀ i, IsChartAt Y x (R i) (ξ i)) ∧
    ∀ (V C : Type) [CommRing V] [IsLocalRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
      [IsAlgClosed C] [CharZero C] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 →
      ∀ y : Sp V ⟶ Y.X, y (IsLocalRing.closedPoint V) = x →
        Set.range (spMap (algebraMap V C) ≫ y) ⊆ abLocus Y.t.G →
        ∃ (i : Fin n) (f : R i →+* V), IsLocalHom f ∧ spMap f ≫ ξ i = y

def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)

theorem IsChartAt.unif {Y : Model Xo c β} (hY : Y.N3) {x : Y.X} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsChartAt Y x R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by
  obtain ⟨h0, h1, h2, h3, -, h5, t, m, S, hS⟩ := h
  exact ⟨t, m, hY R h1 h2 h3 ξ t m h5 ⟨S, hS⟩⟩

end OneModel

def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'

def CoveringLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, (Y i).SplitFibres → CoveredByCharts (Y i) p

def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)

def CoveringAndSmoothness : Prop := CoveringLemma ∧ SmoothnessLemma

theorem goodPrime_iff (l : Level H) {p : ℕ} (hp : p.Prime) :
    GoodPrime l p ↔ ¬ (p : ℤ) ∣ discr E ∧ ¬ p ∣ l.M' := by
  unfold GoodPrime
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)]

end GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
