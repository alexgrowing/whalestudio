import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleSectionsGlueHomogeneous
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_sections_glue_homogeneous : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ) (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing | exact GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing | (intros; apply GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing <;> assumption)
