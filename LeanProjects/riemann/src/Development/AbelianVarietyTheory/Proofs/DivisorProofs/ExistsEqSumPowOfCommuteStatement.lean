import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommute
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  first | exact @GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | exact GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | (intros; apply GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute <;> assumption)
