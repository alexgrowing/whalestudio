import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.WeilBound.CoreStatements.FlagImmersions.FlagDegreeLinearFunctionals
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem degFl_Sh_Tot_linear : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = degFl F) ∧ (∀ (j : ℕ) (τ : Ψ), ∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = Sh j τ F) ∧ (∀ τ : Ψ, ∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = Tot τ F) ∧ ∀ (d : ℕ) (F : RP Ψ N), F.IsHomogeneous d → d ≠ dimFl Ψ N → degFl F = 0 :=
  @RootFieldNumerics.degFl_Sh_Tot_linear_and_degFl_eq_zero_off_dim

end GlobalTheory.CompanionTheory.Ar.Top
