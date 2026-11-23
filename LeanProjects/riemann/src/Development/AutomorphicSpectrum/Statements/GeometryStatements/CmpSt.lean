import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

def CmpSt : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k)
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ)
    (Re₁ : Realis S₁ (mCoordIdeal (y ∘ v₁))) (Re₂ : Realis S₂ (mCoordIdeal (y ∘ v₂)))
    (β : MRing ι) (b : K → ℕ),
    IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsArithVar (mCoordIdeal y) (D + 1) →
    IsMultiHomog β b → β ∉ mCoordIdeal y →
    AlgOver Re₁ → AlgOver Re₂ → (∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a) →
    ∀ w : Fin (D + 1) → σ, Tendsto (fun t =>
      (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℝ) *
          II K₁ ι₁ (mCoordIdeal (y ∘ v₁)) (D + 1) (fun j => Re₁.line (w j) t) -
        (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℝ) *
          II K₂ ι₂ (mCoordIdeal (y ∘ v₂)) (D + 1) (fun j => Re₂.line (w j) t)) (𝓝[>] 0) (𝓝 0)

end GlobalTheory.CompanionTheory.Ar.Cmp
