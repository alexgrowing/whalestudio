import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzQuasiIntegralCriterion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.katz_quasi_integral_criterion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f : MvPowerSeries (Fin d) (Fr p k), (∀ i, ∃ w : WittVector p k, lin f i = algebraMap (WittVector p k) (Fr p k) w) → cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ 1 → f ∈ quasiInt p k (Fin d) := by
  first | exact @GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int | exact GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int | (intros; apply GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int <;> assumption)
