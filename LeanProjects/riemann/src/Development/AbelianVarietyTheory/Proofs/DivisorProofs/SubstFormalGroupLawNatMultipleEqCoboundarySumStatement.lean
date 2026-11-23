import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (g : MvPowerSeries (Fin d) R) (n : ℕ), subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g + ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  first | exact @GlobalTheory.QLog.subst_nmul_eq | exact GlobalTheory.QLog.subst_nmul_eq | (intros; apply GlobalTheory.QLog.subst_nmul_eq <;> assumption)
