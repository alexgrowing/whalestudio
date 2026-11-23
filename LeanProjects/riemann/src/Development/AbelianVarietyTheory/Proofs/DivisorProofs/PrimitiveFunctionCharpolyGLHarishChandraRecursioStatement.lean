import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursio
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F), psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  first | (exact @GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (exact GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (intros; apply GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc <;> assumption)
