import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_complex_homotopy_data : ∀ (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁), a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ → ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁), π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧ j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology | exact GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology <;> assumption)
