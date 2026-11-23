import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coboundary_representative_cocycle_rules : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → Function.Injective (algebraMap O E) → ∀ (f : MvPowerSeries (Fin d) E) (κ : MvPowerSeries (Fin d ⊕ Fin d) O), map (algebraMap O E) κ = cob1 (up E μ) f → IsCoc μ κ ∧ (constantCoeff f = 0 → constantCoeff κ = 0) ∧ ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect μ n f → cob1 μ s = (n : O) • κ - pull2 (nmul μ n) κ ∧ ∀ (m : ℕ) (t u : MvPowerSeries (Fin d) O), map (algebraMap O E) t = defect μ m f → map (algebraMap O E) u = defect μ (m * n) f → u = (m : O) • s + subst (nmul μ n) t := by
  first | exact @GlobalTheory.QLog.integral_cob_defect_rules | exact GlobalTheory.QLog.integral_cob_defect_rules | (intros; apply GlobalTheory.QLog.integral_cob_defect_rules <;> assumption)
