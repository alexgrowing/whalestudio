import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobHecke

theorem isHecke_globFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f →
    IsHecke (globLev S K') (globFn S f) := by
  intro E _ _ _ hU n _ S hS K' hK' f hf
  refine ⟨?_, globFn_inv S K' f fun w => (hf.1 w).2⟩
  have hC : ∀ᶠ w in cofinite, tsupport (f w) = (KL n w : Set (UL n w)) := by
    filter_upwards [hK'.2, hf.2] with w h1 h2
    have ho : IsOpen (KL n w : Set (UL n w)) := h1 ▸ (hK'.1 w).1
    have hc : IsClosed (KL n w : Set (UL n w)) := Subgroup.isClosed_of_isOpen _ ho
    rw [h2, tsupport, Set.support_indicator]
    have : Function.support (1 : UL n w → ℂ) = Set.univ := by
      ext x; simp
    rw [this, Set.inter_univ, hc.closure_eq]
  have hcpt := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => tsupport (f w)) (fun w => (hf.1 w).1) hC
  refine HasCompactSupport.intro hcpt fun x hx => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  have hfin : (S ∩ Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf.2
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u ⟨-, hu⟩ ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  rw [finprod_mem_eq_prod _ hfin]
  have h0 : f w (toSub (UL n w) (cLoc w (x : UA E n))) = 0 := image_eq_zero_of_notMem_tsupport hxw
  refine Finset.prod_eq_zero (i := w) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw, ?_⟩
  show f w _ ≠ 1
  rw [h0]
  exact zero_ne_one

end GlobalTheory.BCT.GlobHecke
