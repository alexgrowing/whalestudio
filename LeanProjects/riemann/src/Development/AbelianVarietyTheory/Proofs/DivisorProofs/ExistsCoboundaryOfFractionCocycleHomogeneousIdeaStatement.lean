import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdea
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (G i).IsHomogeneous (d + N')) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  first | exact @GlobalTheory.exists_coboundary_of_cocycle_homogeneous | exact GlobalTheory.exists_coboundary_of_cocycle_homogeneous | (intros; apply GlobalTheory.exists_coboundary_of_cocycle_homogeneous <;> assumption)
