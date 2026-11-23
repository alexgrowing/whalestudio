import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoice
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_at_gen_independent_choice : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ),
    IsCptGen ξ → e₀ ≠ 0 → CoordsAt ξ y z w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → (∀ k, w ⟨k, c₁ k⟩ ≠ 0) →
    ValAt ξ z (τ / gen y a e₀ c₀) u → ValAt ξ z (τ / gen y a e₀ c₁) u' →
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change <;> assumption)
