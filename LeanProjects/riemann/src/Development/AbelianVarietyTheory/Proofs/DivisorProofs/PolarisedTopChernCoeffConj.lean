import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_prod_perm_mul_comm {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (A : Fin n → Matrix r r ℂ)
    (P : Matrix r r ℂ) (π : Equiv.Perm (Fin n)) :
    ∑ p : Fin n → r, ∏ i, (A i * P) (p i) (p (π i)) = ∑ p : Fin n → r, ∏ i, (P * A i) (p i) (p (π i)) := by
  simp only [Matrix.mul_apply]
  have h1 : ∀ f : Fin n → r → ℂ, ∏ i, ∑ j, f i j = ∑ s : Fin n → r, ∏ i, f i (s i) := fun f => by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [h1]
  rw [Finset.sum_comm]
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl r)) _ _ fun t => ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.prod_mul_distrib, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp, id]
  rw [mul_comm, Equiv.prod_comp π fun i => P (t i) (p i)]

theorem mixTop_conj {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ)
    (hP : IsUnit P.det) : mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  unfold mixTop
  congr 1
  have hdet : ∀ M : Fin n → Fin n → ℂ, (Matrix.of M).det =
      ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, M i (w i) := fun M => by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [← Finset.mul_sum]
  congr 2
  rw [sum_prod_perm_mul_comm (fun i => P⁻¹ * K i (u i) (w i)) P π]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

end GlobalTheory.GoodTop
