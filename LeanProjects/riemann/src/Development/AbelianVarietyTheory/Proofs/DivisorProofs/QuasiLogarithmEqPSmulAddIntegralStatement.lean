import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmEqPSmulAddIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ f ∈ quasiLog p h, ∀ b, Red p (cob1 (fun i => Katz.lift p (μ i)) f) (cob1 μ b) → RedV p (lin f) (lin b) → ∃ g ∈ quasiLog p h, f - (p : WittVector p k) • g ∈ intBy p k (Fin d) 1 := by
  first | exact @GlobalTheory.Katz.quasiLog_eq_p_smul_add_int | exact GlobalTheory.Katz.quasiLog_eq_p_smul_add_int | (intros; apply GlobalTheory.Katz.quasiLog_eq_p_smul_add_int <;> assumption)
