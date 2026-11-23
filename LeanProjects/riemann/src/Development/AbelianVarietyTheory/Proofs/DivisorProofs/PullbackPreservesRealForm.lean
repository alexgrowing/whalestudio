import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

noncomputable section

open GlobalTheory.CxForm Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm.RealPull

variable {n m : ℕ}

def cjCoef (n : ℕ) : Alt n →ₛₗ[starRingEnd ℂ] Alt n where
  toFun α := ∑ S, conj ((bas n).repr α S) • bas n S
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem repr_cjCoef (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (cjCoef n α) S = conj ((bas n).repr α S) := by
  change (bas n).repr (∑ S, conj ((bas n).repr α S) • bas n S) S = _
  rw [Module.Basis.repr_sum_self]

theorem cjCoef_bas (S : Finset (Fin (n + n))) : cjCoef n (bas n S) = bas n S := by
  refine (bas n).ext_elem fun T => ?_
  rw [repr_cjCoef]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem bas_mul_of_not_disjoint {S T : Finset (Fin (n + n))} (h : ¬ Disjoint S T) : bas n S * bas n T = 0 :=
  ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
    (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h

theorem cjCoef_mul (a b : Alt n) : cjCoef n (a * b) = cjCoef n a * cjCoef n b := by
  have key (S T) : cjCoef n (bas n S * bas n T) = bas n S * bas n T := by
    by_cases h : Disjoint S T
    · obtain ⟨ε, e⟩ := bas_mul h
      rw [e, Units.smul_def, map_zsmul, cjCoef_bas]
    · rw [bas_mul_of_not_disjoint h, map_zero]
  rw [← (bas n).sum_repr a, ← (bas n).sum_repr b]
  generalize (bas n).repr a = u
  generalize (bas n).repr b = w
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smulₛₗ, key, cjCoef_bas, map_mul]

theorem cjCoef_one : cjCoef n 1 = 1 := by rw [← bas_empty, cjCoef_bas]

theorem cjCoef_ι (u : Fin n ⊕ Fin n → ℂ) :
    cjCoef n (ExteriorAlgebra.ι ℂ u) = ExteriorAlgebra.ι ℂ (fun i => conj (u i)) := by
  have h (w : Fin n ⊕ Fin n → ℂ) : ExteriorAlgebra.ι ℂ w = ∑ i, w i • bas n {finSumFinEquiv i} := by
    simp only [bas_singleton, ← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  simp only [h, map_sum, map_smulₛₗ, cjCoef_bas]

theorem isReal_iff (α : Alt n) : IsReal α ↔ swap α = cjCoef n α := by
  simp only [IsReal, ← repr_cjCoef]
  exact ⟨(bas n).ext_elem, fun h _ => by rw [h]⟩

def pullConj (L : V n →L[ℂ] V m) : Alt m →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (fromBlocks (of fun b a => conj (L (coordVec b) a)) 0 0
    (of fun b a => L (coordVec b) a)))

theorem swap_pull (L : V n →L[ℂ] V m) (α : Alt m) : swap (pull L α) = pullConj L (swap α) := by
  have : swap.comp (pull L) = (pullConj L).comp swap := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun u => ?_)
    simp only [swap, pull, pullConj, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with i | i <;>
      simp [LinearMap.funLeft_apply, Matrix.toLin'_apply, mulVec, dotProduct, Fintype.sum_sum_type]
  exact DFunLike.congr_fun this α

theorem cjCoef_pull (L : V n →L[ℂ] V m) (α : Alt m) : cjCoef n (pull L α) = pullConj L (cjCoef m α) := by
  induction α using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, map_smulₛₗ, cjCoef_one]
  | ι u =>
    simp only [pull, pullConj, ExteriorAlgebra.map_apply_ι, cjCoef_ι]
    congr 1
    funext i
    rcases i with i | i <;>
      simp [Matrix.toLin'_apply, mulVec, dotProduct, Fintype.sum_sum_type]
  | mul a b ha hb => simp only [map_mul, cjCoef_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem isReal_pull (n m : ℕ) (L : V n →L[ℂ] V m) (α : Alt m) (h : IsReal α) : IsReal (pull L α) := by
  rw [isReal_iff] at h ⊢
  rw [swap_pull, h, cjCoef_pull]

end GlobalTheory.CxForm.RealPull
