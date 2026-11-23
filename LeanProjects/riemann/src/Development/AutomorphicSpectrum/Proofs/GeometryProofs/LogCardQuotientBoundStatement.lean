import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogCardQuotientBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_quotient_bound : ∀ (L : Type) [Field L] [NumberField L] (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc]
    (F₀ F₁ : Submodule (𝓞 L) Bc) (φ : F₁ →ₗ[𝓞 L] L) (s : F₁) (m : ℕ) (ρ : FinitePlace L → ℝ),
    F₁.FG → (∀ x, φ x = 0 ↔ (x : Bc) ∈ F₀) → φ s ≠ 0 → 0 < m → (∀ v, 0 < ρ v) → (Function.mulSupport ρ).Finite →
    (∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * ρ v) ∧ ∃ x, v (m : L) * ρ v ≤ v (φ x)) →
    |Real.log (Nat.card (F₁ ⧸ (F₀ ⊔ Submodule.span (𝓞 L) {(s : Bc)}).comap F₁.subtype)) -
      ∑ᶠ v : FinitePlace L, (Real.log (ρ v) - Real.log (v (φ s)))| ≤ Module.finrank ℚ L * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le | exact GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le <;> assumption)
