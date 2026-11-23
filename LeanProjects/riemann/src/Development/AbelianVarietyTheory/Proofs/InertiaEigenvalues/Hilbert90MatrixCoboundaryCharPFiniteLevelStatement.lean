import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R), (∀ g h i j, ρ g (M h i j) = M h i j) → (∀ h i j, M h i j ^ p ^ m = M h i j) → (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧ ∀ g, M g * W.map (ρ g) = W := by
  first | exact @GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | exact GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | (intros; apply GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary <;> assumption)
