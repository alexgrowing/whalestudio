import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundaries
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, Red p g c → Red p (cob2 (fun i => Katz.lift p (μ i)) g) (cob2 μ c) ∧ Red p (swap g) (swap c)) ∧ (∀ b b', Red p b b' → Red p (cob1 (fun i => Katz.lift p (μ i)) b) (cob1 μ b') ∧ RedV p (lin b) (lin b')) ∧ (∀ i, Red p (op (fun i => Katz.lift p (μ i)) x1 (op (fun i => Katz.lift p (μ i)) x2 x3) i) (op μ x1 (op μ x2 x3) i) ∧ Red p (op (fun i => Katz.lift p (μ i)) (op (fun i => Katz.lift p (μ i)) x1 x2) x3 i) (op μ (op μ x1 x2) x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ intBy p k (Fin d ⊕ Fin d) c → cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ c ∧ swap g ∈ intBy p k _ c := by
  first | exact @GlobalTheory.Katz.red_coboundaries | exact GlobalTheory.Katz.red_coboundaries | (intros; apply GlobalTheory.Katz.red_coboundaries <;> assumption)
