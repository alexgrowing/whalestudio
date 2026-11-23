import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltration
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_lift_adic_filtration : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal | exact GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal | (intros; apply GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal <;> assumption)
