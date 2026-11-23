import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffCoeffPowEqOfBox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le : ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  first | exact @GlobalTheory.coeff_coeff_pow_eq_of_box | exact GlobalTheory.coeff_coeff_pow_eq_of_box | (intros; apply GlobalTheory.coeff_coeff_pow_eq_of_box <;> assumption)
