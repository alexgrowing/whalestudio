import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactParabolicUnipotentEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_compact_parabolic_unipotent_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E), ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w ∧ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (GlobalTheory.LeviFubini.sM h w) ≤ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w) := by
  first | exact @GlobalTheory.LeviFubini.IntPts.intPts | exact GlobalTheory.LeviFubini.IntPts.intPts | (intros; apply GlobalTheory.LeviFubini.IntPts.intPts <;> assumption)
