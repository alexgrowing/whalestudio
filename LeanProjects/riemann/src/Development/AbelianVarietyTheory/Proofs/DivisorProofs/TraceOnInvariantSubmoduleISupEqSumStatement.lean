import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V) (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) → trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  first | exact @GlobalTheory.BCT.trOn_iSup_eq_sum | exact GlobalTheory.BCT.trOn_iSup_eq_sum | (intros; apply GlobalTheory.BCT.trOn_iSup_eq_sum <;> assumption)
