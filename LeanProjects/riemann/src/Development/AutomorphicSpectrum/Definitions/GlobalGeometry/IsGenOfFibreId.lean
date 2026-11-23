import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.M0

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsGenOfFibre {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) (a : O) (w : X) : Prop :=
  a ∈ (s w).asIdeal ∧ ∀ w' : X, a ∈ (s w').asIdeal → w' ⤳ w → w' = w

def NoBdryComp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ w : Y.X, IsGenOfFibre Y.s (p : O) w → w ∈ abLocus Y.t.G

def TorsRat {W : Type} [CommRing W] [IsDomain W] (G : Over (Sp W)) [GrpObj G] (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing W) F] (x : Out.TF (R := W) F ⟶ G), x ^ k = 1 →
    ∃ x₀ : Out.TK W ⟶ G, x.left = Out.jFK (R := W) F ≫ x₀.left

def QkRat {W : Type} [CommRing W] [IsDomain W] (D : Out.DegPre W) (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (q : Out.QkPt D F k),
    ∃ q₀ : Out.QkPt D (FractionRing W) k, QkExt (algebraMap (FractionRing W) F) q₀ q

end GlobalTheory.CompanionTheory.Ar.M0
