import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CartanRefl

open Matrix

variable {n : ℕ}

theorem herm {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.map star = Mᵀ) (x y : Fin n → ℂ) :
    star (x ⬝ᵥ M *ᵥ star y) = y ⬝ᵥ M *ᵥ star x := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by
    simpa using congrFun (congrFun hM i) j
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.CartanRefl
