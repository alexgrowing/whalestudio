import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w), U ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) ∧ U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 ∧ ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.LeviDesc.ConjStab.exists_stab | exact GlobalTheory.LeviDesc.ConjStab.exists_stab | (intros; apply GlobalTheory.LeviDesc.ConjStab.exists_stab <;> assumption)
