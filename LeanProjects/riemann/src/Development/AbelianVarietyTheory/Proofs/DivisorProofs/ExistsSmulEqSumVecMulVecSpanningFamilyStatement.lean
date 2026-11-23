import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_eq_sum_vecMulVec_spanning_family : ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ), (L.map (Int.cast : ℤ → ℝ)).PosDef → ∃ (D m : ℕ) (a : Fin m → Fin r → ℤ), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ (D : ℤ) • L = ∑ i, Matrix.vecMulVec (a i) (a i) := by
  first | exact @GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span | exact GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span | (intros; apply GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span <;> assumption)
