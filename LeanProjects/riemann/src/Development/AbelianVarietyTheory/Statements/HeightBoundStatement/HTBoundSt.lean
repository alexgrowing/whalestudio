import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

def HTBoundSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CompleteSpace C] [CharZero C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (xO : Sp ↥(intO C) ⟶ X), (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO) → ∀ v ∈ latHT t p (spMap (intO C).subtype ≫ xO), ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → spMap (epsMul a) ≫ v ∈ latDR t (spMap (intO C).subtype ≫ xO)

end GlobalTheory.ShFam.Pad
