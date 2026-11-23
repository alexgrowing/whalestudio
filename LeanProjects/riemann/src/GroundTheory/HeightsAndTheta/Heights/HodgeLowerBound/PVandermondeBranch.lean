import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVandermondeBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Polynomial Finset Equiv

theorem VandermondeBranch.det_vandermonde_eq_descPochhammer {j : ℕ} (w : Fin j → ℚ) :
    (Matrix.vandermonde w).det =
      (Matrix.of (fun r s : Fin j => (descPochhammer ℚ (s : ℕ)).eval (w r))).det :=
  Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde w (fun s => descPochhammer ℚ (s : ℕ))
    (fun _ => descPochhammer_natDegree (R := ℚ) _) (fun _ => monic_descPochhammer (R := ℚ) _)

theorem VandermondeBranch.mul_eval_sub_one (k : ℕ) (x : ℚ) :
    x * (descPochhammer ℚ k).eval (x - 1) = (descPochhammer ℚ k).eval x * (x - k) := by
  rw [← descPochhammer_succ_eval, descPochhammer_succ_left]
  simp [eval_comp]

theorem VandermondeBranch.term {j : ℕ} (v : Fin j → ℚ) (σ : Perm (Fin j)) (i₀ : Fin j) :
    v (σ i₀) * ∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v (σ i₀) (v (σ i₀) - 1) (σ i)) =
      (∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval (v (σ i))) * (v (σ i₀) - (i₀ : ℕ)) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i₀), ← Finset.mul_prod_erase univ _ (mem_univ i₀)]
  have hrest : ∏ i ∈ univ.erase i₀, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v (σ i₀) (v (σ i₀) - 1) (σ i)) =
      ∏ i ∈ univ.erase i₀, (descPochhammer ℚ (i : ℕ)).eval (v (σ i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : σ i ≠ σ i₀ := fun h => (Finset.ne_of_mem_erase hi) (σ.injective h)
    rw [Function.update_of_ne hne]
  rw [hrest, Function.update_self, ← mul_assoc, VandermondeBranch.mul_eval_sub_one]
  ring

theorem VandermondeBranch.proof : VandermondeBranch.Statement := by
  intro j v
  simp only [VandermondeBranch.det_vandermonde_eq_descPochhammer]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ a, v a * (↑↑(Perm.sign σ) * ∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v a (v a - 1) (σ i))) =
      ↑↑(Perm.sign σ) * (v a * ∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v a (v a - 1) (σ i))) := fun a => by ring
  simp only [h1]
  rw [← Finset.mul_sum, ← Equiv.sum_comp σ]
  simp only [VandermondeBranch.term, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Equiv.sum_comp σ v]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
