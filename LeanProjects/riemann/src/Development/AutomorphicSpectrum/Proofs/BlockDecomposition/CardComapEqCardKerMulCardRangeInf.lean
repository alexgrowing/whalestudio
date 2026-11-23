import Mathlib

namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_eq_card_ker_mul_card_range_inf :
    ∀ (R A X : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A] [AddCommGroup X]
      [Module R X] (f : A →ₗ[R] X) (U : Submodule R X),
      Nat.card ↥(U.comap f) = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f ⊓ U) := by
  intro R A X _ _ _ _ _ _ f U
  have hker : LinearMap.ker (f.domRestrict (U.comap f)) ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1.1, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩
      invFun := fun y => ⟨⟨y.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.mp y.2]
          exact U.zero_mem⟩, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hrange : LinearMap.range (f.domRestrict (U.comap f)) = LinearMap.range f ⊓ U := by
    rw [LinearMap.range_domRestrict, Submodule.map_comap_eq]
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (f.domRestrict (U.comap f))),
    Nat.card_congr hker, Nat.card_congr (f.domRestrict (U.comap f)).quotKerEquivRange.toEquiv,
    hrange]

end GlobalTheory.CompanionTheory.Counting
