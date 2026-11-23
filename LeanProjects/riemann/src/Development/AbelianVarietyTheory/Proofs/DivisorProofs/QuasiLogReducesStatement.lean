import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReduces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLog_reduces_to_cocycle : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ f ∈ quasiLog p h, ∃ c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w) ∧ ∀ f ∈ quasiLog p h, ∀ c, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c → IsCoc μ c := by
  first | exact @GlobalTheory.quasiLog_reduces | exact GlobalTheory.quasiLog_reduces | (intros; apply GlobalTheory.quasiLog_reduces <;> assumption)
