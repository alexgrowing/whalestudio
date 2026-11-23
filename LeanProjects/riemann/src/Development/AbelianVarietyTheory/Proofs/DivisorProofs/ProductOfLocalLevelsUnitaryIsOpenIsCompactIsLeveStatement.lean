import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S (KL n) : Set (finU E n)) ∧ IsCompact (globLev S (KL n) : Set (finU E n)) ∧ IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  first | exact @GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | exact GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | (intros; apply GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel <;> assumption)
