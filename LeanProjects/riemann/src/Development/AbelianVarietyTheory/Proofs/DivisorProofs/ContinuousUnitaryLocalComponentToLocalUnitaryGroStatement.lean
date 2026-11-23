import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryLocalComponentToLocalUnitaryGro
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ w : Pl E, Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) := by
  first | exact @GlobalTheory.BCT.toSub_cLoc_fin_continuous | exact GlobalTheory.BCT.toSub_cLoc_fin_continuous | (intros; apply GlobalTheory.BCT.toSub_cLoc_fin_continuous <;> assumption)
