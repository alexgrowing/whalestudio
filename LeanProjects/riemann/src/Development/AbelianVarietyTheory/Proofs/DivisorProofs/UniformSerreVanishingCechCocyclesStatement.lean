import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocycles
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_serre_vanishing_cech_cocycles : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, coeff m (F i j) ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, coeff m (G i) ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  first | exact @GlobalTheory.uniformSerre_cocycle | exact GlobalTheory.uniformSerre_cocycle | (intros; apply GlobalTheory.uniformSerre_cocycle <;> assumption)
