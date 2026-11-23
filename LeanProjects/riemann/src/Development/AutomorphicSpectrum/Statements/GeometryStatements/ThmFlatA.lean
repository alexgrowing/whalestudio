import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

def ThmFlatA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) [NumberField c.F] (U : Set ((Xo l).XF c)) (τ : E →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif (Xo l) (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
    1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → (∀ p : ℕ, p.Prime → l.GoodAt p) → IsTypeFn H D.p D.q ty →
    IsClopen U → IsIrreducible U →
    (∀ y : Sp ℂ ⟶ (Xo l).XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P)) →
    ∃ (φ : FrameFn (Xo l) c) (N : LogNorms c.F), IsFlatGen U τ φ FU i ∧ HasNorms U τ φ N ∧ N.IsAdelic

end GlobalTheory.CompanionTheory.Ar.Flat
