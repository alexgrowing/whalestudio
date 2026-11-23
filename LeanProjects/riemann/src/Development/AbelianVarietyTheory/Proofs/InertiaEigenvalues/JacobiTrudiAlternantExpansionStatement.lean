import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_trudi_alternant_expansion : ∀ {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A),
    GlobalTheory.JSW.alternant A m (GlobalTheory.JSW.staircase m) *
                 ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ GlobalTheory.JSW.antiParts m d,
        MvPolynomial.C (GlobalTheory.JSW.jtDet m h l) * GlobalTheory.JSW.alternant A m (fun i => l i + GlobalTheory.JSW.staircase m i) := by
  first | exact @GlobalTheory.JSW.alternant_staircase_mul_antidiagonal | exact GlobalTheory.JSW.alternant_staircase_mul_antidiagonal | (intros; apply GlobalTheory.JSW.alternant_staircase_mul_antidiagonal <;> assumption)
