import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w), g ∈ GlobalTheory.LFun.KGL w n → (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  first | exact @GlobalTheory.CharpolyInt.kint | exact GlobalTheory.CharpolyInt.kint | (intros; apply GlobalTheory.CharpolyInt.kint <;> assumption)
