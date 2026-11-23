import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLsmulEqFinrankMulTrace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lsmul_eq_finrank_mul_trace : ∀ (R Λ M : Type) [CommRing R] [Nontrivial R] [CommRing Λ] [Nontrivial Λ] [Algebra R Λ] [Module.Free R Λ] [Module.Finite R Λ] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower R Λ M] [Module.Free Λ M] [Module.Finite Λ M] (a : Λ), LinearMap.trace R M (Algebra.lsmul R R M a) = (Module.finrank Λ M : R) * Algebra.trace R Λ a := by
  first | exact @GlobalTheory.trace_lsmul_free_eq_finrank_mul_trace | exact GlobalTheory.trace_lsmul_free_eq_finrank_mul_trace | (intros; apply GlobalTheory.trace_lsmul_free_eq_finrank_mul_trace <;> assumption)
