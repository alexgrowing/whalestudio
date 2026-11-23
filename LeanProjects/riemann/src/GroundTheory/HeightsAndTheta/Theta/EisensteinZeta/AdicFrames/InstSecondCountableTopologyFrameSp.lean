import Mathlib

import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open Matrix TensorProduct GroundTheory.Automorphic Topology

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]

attribute [local instance] scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem t2Space_tensor_product [T2Space R] : T2Space (R ⊗[K] E) := t2Space_tensor R

theorem locallyCompactSpace_A [LocallyCompactSpace R] : LocallyCompactSpace (R ⊗[K] E) :=
  (tensorCoordsHomeomorph R (Module.finBasis K E)).isClosedEmbedding.locallyCompactSpace

theorem secondCountableTopology_A [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[K] E) :=
  (tensorCoordsHomeomorph R (Module.finBasis K E)).isEmbedding.secondCountableTopology

section Inverse

variable (K E R) in

abbrev bA :
    Module.Basis (Fin (Module.finrank K E)) R (R ⊗[K] E) :=
  Algebra.TensorProduct.basis R (Module.finBasis K E)

abbrev mulMat : R ⊗[K] E →ₐ[R] Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E)) R :=
  Algebra.leftMulMatrix (bA K E R)

def ofMulMat (M : Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E)) R) : R ⊗[K] E :=
  (bA K E R).equivFun.symm (M *ᵥ (bA K E R).equivFun 1)

theorem ofMulMat_mulMat (z : R ⊗[K] E) : ofMulMat (mulMat (K := K) (E := E) z) = z := by
  rw [ofMulMat, Module.Basis.equivFun_apply, Algebra.leftMulMatrix_mulVec_repr, mul_one,
    ← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]

theorem continuous_mulMat : Continuous (mulMat (K := K) (E := E) (R := R)) :=
  IsModuleTopology.continuous_of_linearMap (mulMat (K := K) (E := E) (R := R)).toLinearMap

theorem continuous_ofMulMat : Continuous (ofMulMat (K := K) (E := E) (R := R)) := by
  have h1 : Continuous (fun v : Fin (Module.finrank K E) → R ↦ (bA K E R).equivFun.symm v) :=
    IsModuleTopology.continuous_of_linearMap (bA K E R).equivFun.symm.toLinearMap
  exact h1.comp (continuous_id.matrix_mulVec continuous_const)

theorem isUnit_iff_isUnit_det_mulMat (z : R ⊗[K] E) :
    IsUnit z ↔ IsUnit (mulMat (K := K) (E := E) z).det := by
  constructor
  · intro hz
    exact (Matrix.isUnit_iff_isUnit_det _).1 (hz.map _)
  · intro hd
    set M := mulMat (K := K) (E := E) z
    have h : z * ofMulMat M⁻¹ = 1 := by
      apply (bA K E R).equivFun.injective
      rw [Module.Basis.equivFun_apply (bA K E R) (z * _), ← Algebra.leftMulMatrix_mulVec_repr,
        ← Module.Basis.equivFun_apply, ofMulMat, LinearEquiv.apply_symm_apply,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
    exact ⟨⟨z, ofMulMat M⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem ringInverse_eq (z : R ⊗[K] E) (hz : IsUnit z) :
    Ring.inverse z = ofMulMat (mulMat (K := K) (E := E) z)⁻¹ := by
  obtain ⟨u, rfl⟩ := hz
  rw [Ring.inverse_unit]
  have : (mulMat (K := K) (E := E) (u : R ⊗[K] E))⁻¹ = mulMat (K := K) (E := E) (↑u⁻¹ : R ⊗[K] E) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← map_mul, Units.inv_mul, map_one]
  rw [this, ofMulMat_mulMat]

variable (hRu : IsOpen {r : R | IsUnit r}) (hRi : ∀ r : R, IsUnit r → ContinuousAt Ring.inverse r)
include hRu in

theorem isOpen_units_A : IsOpen {z : R ⊗[K] E | IsUnit z} := by
  have : {z : R ⊗[K] E | IsUnit z} =
      (fun z ↦ (mulMat (K := K) (E := E) z).det) ⁻¹' {r : R | IsUnit r} := by
    ext z
    exact isUnit_iff_isUnit_det_mulMat z
  rw [this]
  exact hRu.preimage (continuous_mulMat.matrix_det)

include hRu hRi in

theorem continuousAt_inverse_A (z : R ⊗[K] E) (hz : IsUnit z) : ContinuousAt Ring.inverse z := by
  have hd := (isUnit_iff_isUnit_det_mulMat z).1 hz
  have h1 : ContinuousAt (fun w : R ⊗[K] E ↦ ofMulMat (mulMat (K := K) (E := E) w)⁻¹) z := by
    refine continuous_ofMulMat.continuousAt.comp ?_
    exact (continuousAt_matrix_inv _ (hRi _ hd)).comp continuous_mulMat.continuousAt
  refine h1.congr ?_
  filter_upwards [(isOpen_units_A hRu).mem_nhds hz] with w hw
  exact (ringInverse_eq w hw).symm

include hRu in

theorem isOpen_isUnit_det {n : Type*} [Fintype n] [DecidableEq n] :
    IsOpen {M : Matrix n n (R ⊗[K] E) | IsUnit M.det} :=
  (isOpen_units_A hRu).preimage (continuous_id.matrix_det)

include hRu hRi in

theorem continuousAt_matrix_inv_A {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (R ⊗[K] E)) (hM : IsUnit M.det) : ContinuousAt Inv.inv M :=
  continuousAt_matrix_inv M (continuousAt_inverse_A hRu hRi _ hM)

end Inverse

section Spaces

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

instance instIsTopologicalAddGroupFrameSp : IsTopologicalAddGroup (FrameSp K E R ι p) :=
  inferInstanceAs (IsTopologicalAddGroup (ι → Fin p → R ⊗[K] E))

instance instLocallyCompactSpaceFrameSp : LocallyCompactSpace (FrameSp K E R ι p) := by
  have := locallyCompactSpace_A (K := K) (E := E) (R := R)
  exact inferInstanceAs (LocallyCompactSpace (ι → Fin p → R ⊗[K] E))

instance instT2SpaceFrameSp : T2Space (FrameSp K E R ι p) := by
  have := t2Space_tensor_product (K := K) (E := E) (R := R)
  exact inferInstanceAs (T2Space (ι → Fin p → R ⊗[K] E))

instance instSecondCountableTopologyFrameSp : SecondCountableTopology (FrameSp K E R ι p) := by
  have := secondCountableTopology_A (K := K) (E := E) (R := R)
  exact inferInstanceAs (SecondCountableTopology (ι → Fin p → R ⊗[K] E))

theorem isClosed_hermSub :
    IsClosed (hermSub K E R p : Set (Matrix (Fin p) (Fin p) (R ⊗[K] E))) := by
  have := t2Space_tensor_product (K := K) (E := E) (R := R)
  exact isClosed_eq ((continuous_id.matrix_map (continuous_conjBase R)).matrix_transpose)
    continuous_id

instance instIsTopologicalAddGroupHermSp : IsTopologicalAddGroup (HermSp K E R p) :=
  inferInstanceAs (IsTopologicalAddGroup (hermSub K E R p))

instance instLocallyCompactSpaceHermSp : LocallyCompactSpace (HermSp K E R p) := by
  have := locallyCompactSpace_A (K := K) (E := E) (R := R)
  exact (isClosed_hermSub (K := K) (E := E) (R := R) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance instT2SpaceHermSp : T2Space (HermSp K E R p) := by
  have := t2Space_tensor_product (K := K) (E := E) (R := R)
  exact inferInstanceAs (T2Space (hermSub K E R p))

instance instSecondCountableTopologyHermSp : SecondCountableTopology (HermSp K E R p) := by
  have := secondCountableTopology_A (K := K) (E := E) (R := R)
  have : SecondCountableTopology (Matrix (Fin p) (Fin p) (R ⊗[K] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin p → Fin p → R ⊗[K] E))
  exact (Topology.IsEmbedding.subtypeVal (p := fun S ↦ S ∈ hermSub K E R p)).secondCountableTopology

theorem continuous_hermSpMat : Continuous (fun S : HermSp K E R p ↦ S.mat) :=
  continuous_subtype_val

end Spaces

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
