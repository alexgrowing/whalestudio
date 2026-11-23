import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  first | exact @GlobalTheory.BCT.FinPart.norm_emb_entry_le_one | exact GlobalTheory.BCT.FinPart.norm_emb_entry_le_one | (intros; apply GlobalTheory.BCT.FinPart.norm_emb_entry_le_one <;> assumption)
