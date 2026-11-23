import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev TateIsoAt (D : Datum H) (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

def IsFullLevelAt (D : Datum H) (t : SAB H X) (ξ : Sp Ω ⟶ X) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)) :
    Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k), ∃ I : TateIsoAt D t (spMap i ≫ ξ),
    (I.ζ N : k) = i z ∧ ∀ a, (I.ev N a).left = spMap i ≫ (ev a).left

end GlobalTheory.CompanionTheory.Ar.XR
