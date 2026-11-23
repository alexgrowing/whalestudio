import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory

theorem dualForm_ringHom_inv {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : A⁻¹.map f = (A.map f)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one _ (map_zero f) (map_one f)]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [show (A.map f).det = f A.det by rw [RingHom.map_det, RingHom.mapMatrix_apply]]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0
      exact hu (by rw [h0, map_zero])
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']
    ext i j
    simp

theorem dualForm_inv_mem_subfield {K : Type} [Field K] (K0 : Subfield K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ K0) (i j : Fin n) : H⁻¹ i j ∈ K0 := by
  set H0 : Matrix (Fin n) (Fin n) K0 := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hmap : H0.map K0.subtype = H := by ext a b; rfl
  rw [← hmap, ← dualForm_ringHom_inv]
  exact (H0⁻¹ i j).2

theorem isRatHerm_dualFrame (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K)
    (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    IsRatHerm K0 H X → IsRatHerm K0 (H⁻¹)ᵀ (Formalism.HN.dualFrame X) := by
  rintro ⟨hK0, hX⟩
  refine ⟨fun i j => dualForm_inv_mem_subfield K0 H hK0 j i, fun v => ?_⟩
  obtain ⟨hu, hm⟩ := hX v
  have huT : IsUnit ((X v)ᵀ).det := by rwa [Matrix.det_transpose]
  have hD : Formalism.HN.dualFrame X v = ((X v)ᵀ)⁻¹ := rfl
  rw [hD]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    exact huT.ringInverse
  · rw [Matrix.nonsing_inv_nonsing_inv _ huT, Matrix.transpose_map,
      dualForm_ringHom_inv, ← hm, Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv,
      Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.transpose_mul]
    have hcu : IsUnit (X v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
    rw [Matrix.nonsing_inv_nonsing_inv _ hcu]
    congr 1

end GlobalTheory
