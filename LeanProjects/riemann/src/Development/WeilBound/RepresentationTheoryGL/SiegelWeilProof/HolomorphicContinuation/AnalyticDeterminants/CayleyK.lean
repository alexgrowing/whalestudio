import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedDerivativeColumnCaseInt

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem term_p (t : ℤ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (H (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (H (N + 1) t) 0 (analyticAt_determinant_power_zero_int (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl

theorem rec_step (t : ℤ) (N : ℕ) : detD (H (N + 1) t) = ((t : ℂ) + N) * detD (H N t) := by
  rw [detD_fin _ _ (analyticAt_determinant_power_zero_int _ _), detD_fin _ _ (analyticAt_determinant_power_zero_int _ _),
    Finset.univ_perm_fin_succ, ← Finset.univ_product_univ, Finset.sum_map, Finset.sum_product,
    Fin.sum_univ_succ]
  simp only [Equiv.toEmbedding_apply, term_p, Equiv.Perm.decomposeFin.symm_sign, if_pos rfl]
  have h0 : ∀ e : Equiv.Perm (Fin N),
      (iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 (0 : Fin (N + 1)) 1)) 0)
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm ((0 : Fin (N + 1)), e) k.succ) 1) =
      t * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case_int t e
  simp only [h0, if_true, one_mul, Fin.succ_ne_zero, if_false]
  cases N with
  | zero => simp
  | succ M =>
    simp only [iterated_derivative_column_case_int, Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg,
      Int.cast_one, neg_one_mul, neg_mul_neg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_mul, Finset.mul_sum, Finset.mul_sum,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> push_cast <;> ring

theorem capelli_determinant_integer_rising (t : ℤ) : ∀ N : ℕ, detD (H N t) = ∏ i ∈ Finset.range N, ((t : ℂ) + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero_int 0 t)]
    simp [H, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_step, capelli_determinant_integer_rising t N, Finset.prod_range_succ]
    ring

end PositivityTheory.Rg.Sw.LVs.CK

namespace PositivityTheory.Rg.Sw.LVs

theorem kappaFin : KappaFin := fun N t => CK.capelli_determinant_integer_rising t N

end PositivityTheory.Rg.Sw.LVs
