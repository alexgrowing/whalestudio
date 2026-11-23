import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → (∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) → ∃ T : Wsp lam →ₗ[ℂ] (UA E n → ℂ), T ≠ 0 ∧ (∀ w, T w ∈ π) ∧ ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w) := by
  first | exact @GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | exact GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | (intros; apply GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining <;> assumption)
