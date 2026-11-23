import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleOfCharPoly
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_of_char_poly : ∀ (A : Type) [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A), (∀ i ∈ I, H * i ∈ I) → ∀ (N : ℕ) (c q : ℕ → A), c N = 1 → (∀ k ≤ N, c k ∈ Z) → (∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • c k - (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k ∈ I) → IsIntMod Z I H := by
  first | exact @GlobalTheory.isIntMod_of_monic_dvd_affine | exact GlobalTheory.isIntMod_of_monic_dvd_affine | (intros; apply GlobalTheory.isIntMod_of_monic_dvd_affine <;> assumption)
