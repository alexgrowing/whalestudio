import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplCons

theorem J_mulVec_inl {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inl i) = -v (Sum.inr i) := by
  simp [Matrix.J, fromBlocks_mulVec, neg_mulVec]

theorem J_mulVec_inr {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inr i) = v (Sum.inl i) := by
  simp [Matrix.J, fromBlocks_mulVec]

theorem symplOmega_eq_sum {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) :
    symplOmega u v = ∑ i, (u (Sum.inr i) * v (Sum.inl i) - u (Sum.inl i) * v (Sum.inr i)) := by
  unfold symplOmega dotProduct
  rw [Fintype.sum_sum_type]
  simp only [J_mulVec_inl, J_mulVec_inr, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib]
  ring

end PSymplCons

open PSymplCons in

theorem SymplCons.proof : SymplCons.Statement := by
  intro R _ n
  refine ⟨fun u => ?_, fun p q p' q' w w' => ?_⟩
  · funext x
    rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons, symplTail]
  · rw [symplOmega_eq_sum, symplOmega_eq_sum, Fin.sum_univ_succ]
    simp [symplCons]

end GroundTheory.Heights₂.Heights
