import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqZeroOfEvAEqZeroOfLeFinrank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (d q : ℕ) (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (J : Ideal A), Function.Surjective (MvPolynomial.aeval (R := K) x) → (∀ i, x i ^ q ∈ J) → q ^ d ≤ Module.finrank K (A ⧸ J) → ∀ f : MvPowerSeries (Fin d) K, evA K x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < q → coeff α f = 0 := by
  first | exact @GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank | exact GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank | (intros; apply GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank <;> assumption)
