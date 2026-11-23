import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTrace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_trace_eq_mul_algebra_trace : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (a : Λ), (ρ a).trace = (N : ℤ_[p]) * Algebra.trace ℤ_[p] Λ a := by
  first | exact @GlobalTheory.traceOnLattice_eq_rank_mul_trace | exact GlobalTheory.traceOnLattice_eq_rank_mul_trace | (intros; apply GlobalTheory.traceOnLattice_eq_rank_mul_trace <;> assumption)
