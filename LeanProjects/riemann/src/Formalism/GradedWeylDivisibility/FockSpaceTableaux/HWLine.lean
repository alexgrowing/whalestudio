import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line : HWLine := by
  intro K _ _ r n hn ν hν f hf hraise
  have hfP := (dualWeylPoint K r n ν f).mp hf
  have hhP := (dualWeylPoint K r n ν (hw K hn ν)).mp (hwMem K r n hn ν hν)
  have hid : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idPoint K r n (a, j) = 0 := by
    intro a j h
    simp [idPoint, h]
  have hP1 : ∏ v, idPoint K r n v ^ (lhwline_mnu hn ν) v = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨a, j⟩ := v
    rw [lhwline_mnu_apply]
    by_cases h : a.val = j.val <;> simp [idPoint, h]
  have hcf : eval (idPoint K r n) f = coeff (lhwline_mnu hn ν) f := by
    rw [lhwline_diag hn ν f hfP.1 _ hid, hP1, mul_one]
  have hch : coeff (lhwline_mnu hn ν) (hw K hn ν) = 1 := by
    have h1 := lhwline_diag hn ν (hw K hn ν) hhP.1 _ hid
    rw [hP1, mul_one] at h1
    rw [← h1]
    simp [hw, eval_idPoint_lpMinor]
  set c := eval (idPoint K r n) f with hc
  refine ⟨c, ?_⟩
  have hgw : IsWeightedHomogeneous (colW r n) (f - c • hw K hn ν) ν := by
    have h1 : f ∈ weightedHomogeneousSubmodule K (colW r n) ν :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP.1
    have h2 : hw K hn ν ∈ weightedHomogeneousSubmodule K (colW r n) ν :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hhP.1
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (Submodule.sub_mem _ h1 (Submodule.smul_mem _ c h2))
  have hg0 : f - c • hw K hn ν = 0 := by
    apply lhwline_vanish
    · intro a b hab
      rw [map_sub, map_smul, lhwline_rowGen_eq a b f (hraise a b hab),
        lhwline_rowGen_eq a b (hw K hn ν) (fun k hk => hwRaise K r n hn ν a b k hab hk)]
      simp [Polynomial.smul_C]
    · intro l j hlj c'
      rw [map_sub, map_smul, hfP.2 l j hlj c', hhP.2 l j hlj c']
    · intro D hD
      rw [lhwline_diag hn ν _ hgw D hD, coeff_sub, coeff_smul, hch, ← hcf]
      simp
  exact sub_eq_zero.mp hg0

end Formalism.GradedWeylDivisibility
