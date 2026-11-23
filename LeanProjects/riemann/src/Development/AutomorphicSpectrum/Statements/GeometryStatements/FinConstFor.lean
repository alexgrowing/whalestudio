import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

def IsHostRange {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H ∧
    ∃ q₁ : ℕ, q₁.Prime ∧ ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ discr E → ℓ = 2 ∨ ℓ = q₁ ∨ ℓ = H.d

def FinConstFor {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : Prop :=
  ∀ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ)
    (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → Function.Injective β →
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → Y.SplitFibres → Y.N3 → Z.IsGeom → FlatOnModel Z τ φ →
    IsLineFn U τ φ → ∃ t : ℝ, HasFinNorm U τ φ p κ t

def FinConst : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsHostRange H → FinConstFor H

def FinConstAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), FinConstFor H

theorem FinConstAll.finConst (h : FinConstAll) : FinConst := fun E _ _ _ H _ => h E H

end GlobalTheory.CompanionTheory.Ar.Flat
