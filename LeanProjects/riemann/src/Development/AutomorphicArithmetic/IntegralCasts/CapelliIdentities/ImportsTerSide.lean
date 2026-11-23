import Mathlib

theorem UpperTheory.Reformulated.B.Qf12.lift_ex :
    ∀ {A M Q Q' : Type} [inst : CommRing A] [inst_1 : AddCommGroup M]
    [inst_2 : AddCommGroup Q] [inst_3 : AddCommGroup Q'] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module A Q]
    [inst_6 : _root_.Module A Q'] (π : M →ₗ[A] Q),
    Function.Surjective (⇑π : M → Q) →
      ∀ (g : M →ₗ[A] Q'),
        (∀ (m : M), (π : M → Q) m = (0 : Q) → (g : M → Q') m = (0 : Q')) →
          ∃ (q : Q →ₗ[A] Q'), ∀ (m : M), (q : Q → Q') ((π : M → Q) m) = (g : M → Q') m := by
  intro A M Q Q' _ _ _ _ _ _ _ π hπ g hg
  have hle : LinearMap.ker π ≤ LinearMap.ker g := fun m hm =>
    LinearMap.mem_ker.mpr (hg m (LinearMap.mem_ker.mp hm))
  refine ⟨((LinearMap.ker π).liftQ g hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun m => ?_⟩
  have h : (π.quotKerEquivOfSurjective hπ).symm (π m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
