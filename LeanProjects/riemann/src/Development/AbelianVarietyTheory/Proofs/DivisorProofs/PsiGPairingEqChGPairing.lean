import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursioStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem psiG_pairing_eq_chG_pairing : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ)
    (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  intro F _ _ S n Y hY hF
  have hfin : Finite (GL (Fin n) F) := inferInstance
  have hfs : ∀ f : GL (Fin n) F → ℂ, (Function.support f).Finite := fun f => Set.toFinite _
  have hz : ∀ a ∈ Finset.range n,
      ∑ᶠ x, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) = 0 := by
    intro a ha
    have ha' : a < n := Finset.mem_range.mp ha
    exact GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer F a (n - a) n (by omega) (by omega) (psiG S a) Y hY hF
  have hrec : ∀ x, psiG S n x * star (Y x) = chG S n x * star (Y x)
      - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) := by
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n x, sub_mul, Finset.sum_mul]
  simp_rw [hrec]
  rw [finsum_sub_distrib (hfs _) (hfs _), finsum_sum_comm (Finset.range n) _ (fun a _ => hfs _),
    Finset.sum_eq_zero hz, sub_zero]

end GlobalTheory
