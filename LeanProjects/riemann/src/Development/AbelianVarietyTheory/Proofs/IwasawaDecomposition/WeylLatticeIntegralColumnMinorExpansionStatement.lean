import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeIntegralColumnMinorExpansion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylLattice_integral_columnMinor_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  first | exact @GlobalTheory.WeylIntExpansion.weyl_int_expansion | exact GlobalTheory.WeylIntExpansion.weyl_int_expansion | (intros; apply GlobalTheory.WeylIntExpansion.weyl_int_expansion <;> assumption)
