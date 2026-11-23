import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefs

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

def HolCoord : Prop :=
  ∀ (Z : Scheme.{0}) (n g : ℕ) (B : Set (Fin n → ℂ)) (e : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z)) (A : Type) [CommRing A]
    (v : Sp (DualNumber A) ⟶ Z) (ψ : (Fin n → ℂ) → (A →+* ℂ)) (w : (Fin n → ℂ) → Fin g → ℂ), IsOpen B →
    IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e bz.1 bz.2) →
    (∀ a, DifferentiableOn ℂ (fun t => ψ t a) B) →
    (∀ t ∈ B, IsDerivAt0 (e t) (w t) (spMap (dualMap (ψ t)) ≫ v)) →
    (∀ t ∈ B, ∀ w₁ w₂ u, IsDerivAt0 (e t) w₁ u → IsDerivAt0 (e t) w₂ u → w₁ = w₂) →
    ∀ t₀ ∈ B, AnalyticAt ℂ w t₀

end SheetDecomposition
