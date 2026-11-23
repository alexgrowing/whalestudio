import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMul
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupAverage_prod_mul_eq_mul : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  first | exact @GlobalTheory.AvgProd.avg_prod | exact GlobalTheory.AvgProd.avg_prod | (intros; apply GlobalTheory.AvgProd.avg_prod <;> assumption)
