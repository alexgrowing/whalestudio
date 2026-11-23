import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelSteinOfComparison
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_stein_of_comparison : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.const_on_fibre | exact GlobalTheory.CompanionTheory.PerfVB.const_on_fibre | (intros; apply GlobalTheory.CompanionTheory.PerfVB.const_on_fibre <;> assumption)
