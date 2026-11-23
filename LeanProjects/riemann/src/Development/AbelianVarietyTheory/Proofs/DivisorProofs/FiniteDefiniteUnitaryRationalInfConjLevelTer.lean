import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelBis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definiteUnitary_rational_inf_conj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite (ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU E n)) := by
  first | exact @GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank | exact GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank | (intros; apply GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank <;> assumption)
