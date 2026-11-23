import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier

namespace GlobalTheory.ConsGeo

abbrev gpt (X : Scheme.{0}) [IsIntegral X] : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

def embDeg {K L : Type} [Field K] [Field L] (θ : K →+* L) : ℕ := letI := θ.toAlgebra; Module.finrank K L

def DvrAgree {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [IsIntegral X₂] (θ : X₂.functionField →+* X₁.functionField)
    (D₁ : CartierDiv X₁) (D₂ : CartierDiv X₂) : Prop :=
  ∀ R : ValuationSubring X₁.functionField, IsDiscreteValuationRing R → ∀ (a : Sp R ⟶ X₁) (b : Sp R ⟶ X₂),
    spMap R.subtype ≫ a = gpt X₁ → spMap R.subtype ≫ b = spMap θ ≫ gpt X₂ →
    ∀ (g₁ : X₁.functionFieldˣ) (g₂ : X₂.functionFieldˣ), D₁.IsEqn (a (closedPoint R)) g₁ →
      D₂.IsEqn (b (closedPoint R)) g₂ → R.valuation g₁ = R.valuation (θ g₂)

theorem DvrAgree.neg {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [IsIntegral X₂] {θ : X₂.functionField →+* X₁.functionField}
    {D₁ : CartierDiv X₁} {D₂ : CartierDiv X₂} (h : DvrAgree θ D₁ D₂) : DvrAgree θ (-D₁) (-D₂) := by
  intro R hR a b ha hb g₁ g₂ h₁ h₂
  have := h R hR a b ha hb g₁⁻¹ g₂⁻¹ (by simpa using h₁.neg) (by simpa using h₂.neg)
  simpa using this

end GlobalTheory.ConsGeo

end
