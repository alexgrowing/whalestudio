import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusLeviMaximalCompactOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_levi_maximal_compact_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), m.1 ∈ GlobalTheory.LFun.KGL w a → m.2 ∈ GlobalTheory.LFun.KGL w b → GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) = 1 := by
  first | exact @GlobalTheory.DeltaOneKGL.deltaHalf_KGL_eq_one | exact GlobalTheory.DeltaOneKGL.deltaHalf_KGL_eq_one | (intros; apply GlobalTheory.DeltaOneKGL.deltaHalf_KGL_eq_one <;> assumption)
