import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

theorem factor_ne_zero_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU E n, (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w n) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  intro E _ _ _ n S K' f hT y hy hne w hw h0
  set F : Pl E → ℂ := fun w => f w (toSub _ (cLoc w y.1)) with hF
  have hev : ∀ᶠ v in cofinite, F v = 1 := by
    filter_upwards [hT.2, hy] with v hv hyv
    simp only [hF, hv]
    have hmem : toSub (UL n v) (cLoc v y.1) ∈ KL n v := by
      unfold toSub
      split_ifs with h
      · exact (Subgroup.mem_subgroupOf).2 hyv
      · exact Subgroup.one_mem _
    exact Set.indicator_of_mem (show toSub (UL n v) (cLoc v y.1) ∈ ((KL n v : Subgroup (UL n v)) : Set (UL n v)) from hmem) _
  have hfin : (Function.mulSupport F).Finite := by
    have := Filter.eventually_cofinite.1 hev
    exact this
  have hfin' : (S ∩ Function.mulSupport F).Finite := hfin.subset Set.inter_subset_right
  apply hne
  show ∏ᶠ v ∈ S, F v = 0
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod F hfin']
  apply Finset.prod_eq_zero (i := w)
  · rw [Set.Finite.mem_toFinset]
    refine ⟨hw, ?_⟩
    rw [Function.mem_mulSupport]
    change f w (toSub _ (cLoc w y.1)) ≠ 1
    rw [h0]; exact zero_ne_one
  · exact h0

end GlobalTheory.BCT.SuppFin
