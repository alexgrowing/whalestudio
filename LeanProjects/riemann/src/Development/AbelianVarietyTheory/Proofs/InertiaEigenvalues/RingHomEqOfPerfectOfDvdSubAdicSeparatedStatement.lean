import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparated
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  first | exact @GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | exact GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | (intros; apply GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub <;> assumption)
