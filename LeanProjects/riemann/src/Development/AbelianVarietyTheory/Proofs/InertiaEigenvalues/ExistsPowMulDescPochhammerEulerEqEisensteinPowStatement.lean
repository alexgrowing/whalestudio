import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulDescPochhammerEulerEqEisensteinPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K → (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  first | exact @GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul | exact GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul | (intros; apply GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul <;> assumption)
