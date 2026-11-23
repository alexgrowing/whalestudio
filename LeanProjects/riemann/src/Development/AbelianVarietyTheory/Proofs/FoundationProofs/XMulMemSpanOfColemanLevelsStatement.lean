import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.XMulMemSpanOfColemanLevels
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_mul_mem_span_of_colemanLevels : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime], IsDomain R → Prime (p : R) → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (h : PowerSeries R) (k c : ℕ), (∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) → ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  first | exact @GlobalTheory.Col.X_mul_mem_span_of_levels | exact GlobalTheory.Col.X_mul_mem_span_of_levels | (intros; apply GlobalTheory.Col.X_mul_mem_span_of_levels <;> assumption)
