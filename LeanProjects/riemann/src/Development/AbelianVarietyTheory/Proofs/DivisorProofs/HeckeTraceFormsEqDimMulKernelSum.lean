import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAtStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_kernSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = dimW lam * kernSum S lam K' f := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf
  rw [GlobalTheory.T.heckeTrace_forms_weight_eq_finrank_mul E hU n hn S hS lam K' hK f hf, GlobalTheory.T.heckeTrace_vectorValued_eq_finite_kernelSum E hU n hn S hS lam K' hK f hf, TrKer.finrank_wsp]
  unfold kernSum
  congr 2
  refine finsum_congr fun q => ?_
  congr 1
  refine finsum_congr fun γ => ?_
  congr 1
  unfold TrKer.wAt chW
  rw [TrKer.trace_piMap]
  exact Finset.prod_congr rfl fun v _ => GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt E n (lam v) γ v

end GlobalTheory.BCT
