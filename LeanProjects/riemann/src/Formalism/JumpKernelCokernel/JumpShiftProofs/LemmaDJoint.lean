import Formalism.JumpKernelCokernel.LemmaDJoint
import Formalism.JumpKernelCokernel.JumpShiftProofs.LenSplit
import Formalism.JumpKernelCokernel.JumpShiftProofs.KerCoker

namespace Formalism.KernelCokernelLengths.QuotientLengthJointLemmas

theorem quot_le (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (B : Type) [AddCommGroup B] [Module O B]
    (πB : Module.End O B) (j : ↥R'' →ₗ[O] B)
    (hstab : R''.map π ≤ R'') (hker : LinearMap.ker j = R'.comap R''.subtype)
    (hj : ∀ (x : ↥R'') (hx : π x ∈ R''), j ⟨π x, hx⟩ = πB (j x)) :
    Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) ≤
      Module.length O (↥(LinearMap.range j) ⧸
        ((LinearMap.range j).map πB).comap (LinearMap.range j).subtype) := by
  set K := (R' ⊔ R''.map π).comap R''.subtype with hK
  set L := ((LinearMap.range j).map πB).comap (LinearMap.range j).subtype with hL
  have hkerK : LinearMap.ker j ≤ K := by
    rw [hker]; exact Submodule.comap_mono le_sup_left
  let ψ : ↥(LinearMap.range j) →ₗ[O] ↥R'' ⧸ K :=
    (Submodule.factor hkerK).comp (j.quotKerEquivRange.symm : ↥(LinearMap.range j) →ₗ[O] ↥R'' ⧸ LinearMap.ker j)
  have hψ : ∀ y : ↥R'', ψ (j.rangeRestrict y) = K.mkQ y := by
    intro y
    have e : j.quotKerEquivRange.symm (j.rangeRestrict y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk j y).symm
    show Submodule.factor hkerK (j.quotKerEquivRange.symm (j.rangeRestrict y)) = K.mkQ y
    rw [e]
    exact Submodule.factor_mk hkerK y
  have hLψ : L ≤ LinearMap.ker ψ := by
    intro m hm
    obtain ⟨b, ⟨x, rfl⟩, hbm⟩ := hm
    have hpx : π x ∈ R'' := hstab ⟨x, x.2, rfl⟩
    have hy : j.rangeRestrict ⟨π x, hpx⟩ = m := Subtype.ext ((hj x hpx).trans hbm)
    rw [LinearMap.mem_ker, ← hy, hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right ⟨x, x.2, rfl⟩
  have hsurj : Function.Surjective (L.liftQ ψ hLψ) := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K z
    exact ⟨L.mkQ (j.rangeRestrict y), by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ]⟩
  exact Module.length_le_of_surjective _ hsurj

end Formalism.KernelCokernelLengths.QuotientLengthJointLemmas

theorem Formalism.KernelCokernelLengths.lemma_D_joint_form : Formalism.KernelCokernelLengths.LemmaDJoint := by
  intro O _ R _ _ π R' R'' B _ _ πB j hle hstab hB hker hj
  have hN : (LinearMap.range j).map πB ≤ LinearMap.range j := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨π x, hstab ⟨x, x.2, rfl⟩⟩, hj x _⟩
  calc _ ≤ _ := Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' hle
    _ ≤ _ := add_le_add le_rfl ((Formalism.KernelCokernelLengths.QuotientLengthJointLemmas.quot_le O R π R' R'' B πB j hstab hker hj).trans
          (Formalism.KernelCokernelLengths.KernelCokernelLemmas.main O B hB πB _ hN))
