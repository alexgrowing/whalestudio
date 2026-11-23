import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem not_isChowForm_zero (hPt : ProjPrimeHasPoint.Statement) {F : Type} [Field F] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) F)} (hW : IsProjPrime W) (g : MvPolynomial (Fin 0 × Fin n) F) :
    ¬ IsChowForm W 0 g := by
  intro hg
  obtain ⟨x, hx, hxW⟩ := hPt F n W hW
  have hunit : g ∣ 1 := by
    rw [eq_C_of_isEmpty g] at hg ⊢
    have hc : coeff 0 g ≠ 0 := fun h => hg.1 (by rw [h, map_zero])
    exact ⟨C (coeff 0 g)⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hinc : (fun _ => 0 : Fin 0 × Fin n → AlgebraicClosure F) ∈ incidence W 0 :=
    ⟨x, hx, hxW, fun i => i.elim0⟩
  have := (hg.2 1).mpr hunit _ hinc
  simp at this

theorem ChowHeightCharacterised.proof (hR : ChowHeightRecursion.Statement)
    (hS : ChowFormSection.Statement) (hMul : ChowHeightMul.Statement) (hPt : ProjPrimeHasPoint.Statement) :
    ChowHeightCharacterised.Statement := by
  intro K _ _ n H J hJ e
  induction e with
  | zero =>
    intro δ I f hI hf hδ
    obtain ⟨u, -, hu⟩ := exists_mem_linForm_not_mem (K := K) hI.isRelevant (S := Set.univ)
      Submodule.span_univ
    obtain ⟨c, hc, g, hg, heq⟩ := hS K n 0 I f (fun j => (u j : K)) hI hf hu
    have hempty : (divCycle I fun j => (u j : K)).support = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro W hW
      exact not_isChowForm_zero hPt (isProjPrime_of_mem_support_divCycle hI _ hW) _ (hg W hW)
    rw [hJ 0 δ I f u hI hf hδ hu, hR K n 0 δ H I f u hI hf hδ hu, hempty, Finset.sum_empty]
    have hne : specFirst f (fun j => (u j : K)) ≠ 0 := by
      rw [heq, hempty, Finset.prod_empty, mul_one]
      exact C_ne_zero.mpr hc
    rw [chowHt_zero_groups_eq_zero H δ hne]
  | succ e ih =>
    intro δ I f hI hf hδ
    obtain ⟨u, -, hu⟩ := exists_mem_linForm_not_mem (K := K) hI.isRelevant (S := Set.univ)
      Submodule.span_univ
    obtain ⟨c, hc, g, hg, heq⟩ := hS K n (e + 1) I f (fun j => (u j : K)) hI hf hu
    rw [hJ (e + 1) δ I f u hI hf hδ hu, hR K n (e + 1) δ H I f u hI hf hδ hu]
    congr 1
    have hδs := hδ.specFirst (fun j => (u j : K))
    have hne : specFirst f (fun j => (u j : K)) ≠ 0 := by
      rw [heq]
      exact mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW =>
        pow_ne_zero _ (hg W hW).1)
    rw [heq] at hδs hne
    obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) _ c g hg hδs hne
    rw [heq, ← hsum, chowHt_C_mul_prod hMul H _ _ _ _ (fun W hW => (hg W hW).1) hc]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [ih (δW W) W (g W) (isProjPrime_of_mem_support_divCycle hI _ hW) (hg W hW) (hδW W hW)]

end

end GroundTheory.Heights₂.Heights
