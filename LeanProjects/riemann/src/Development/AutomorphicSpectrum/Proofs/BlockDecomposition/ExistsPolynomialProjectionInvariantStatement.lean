import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialProjectionInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_projection_invariant : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), γ.charpoly.Separable → (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) → ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' γ) ≤ W → ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq | exact GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq <;> assumption)
