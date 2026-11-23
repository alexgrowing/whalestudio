import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open GlobalTheory.WeilM

namespace GlobalTheory.ArchSchB.TensForm

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β]
  (JA : Matrix α α A) (JB : Matrix β β A)

theorem hTens_add_left (x x' y : Matrix α β A) : hTens c JA JB (x + x') y = hTens c JA JB x y + hTens c JA JB x' y := by
  unfold hTens
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hTens_vmv_right (x : Matrix α β A) (u : α → A) (a : β → A) :
    hTens c JA JB x (Matrix.vecMulVec u a) =
      ∑ i, ∑ j, x i j * (∑ k, JA i k * c (u k)) * (∑ l, JB j l * c (a l)) := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.vecMulVec_apply, map_mul]
  ring

end GlobalTheory.ArchSchB.TensForm
