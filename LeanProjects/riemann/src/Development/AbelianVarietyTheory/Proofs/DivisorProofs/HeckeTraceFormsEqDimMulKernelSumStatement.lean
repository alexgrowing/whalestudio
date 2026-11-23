import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = dimW lam * kernSum S lam K' f := by
  first | exact @GlobalTheory.BCT.trOn_forms_hop_eq_kernSum | exact GlobalTheory.BCT.trOn_forms_hop_eq_kernSum | (intros; apply GlobalTheory.BCT.trOn_forms_hop_eq_kernSum <;> assumption)
