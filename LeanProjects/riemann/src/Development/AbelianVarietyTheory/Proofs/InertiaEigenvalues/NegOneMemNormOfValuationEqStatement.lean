import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEq
import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  first | exact @GlobalTheory.neg_one_mem_norm_of_valuation_eq | exact GlobalTheory.neg_one_mem_norm_of_valuation_eq | (intros; apply GlobalTheory.neg_one_mem_norm_of_valuation_eq <;> assumption)
