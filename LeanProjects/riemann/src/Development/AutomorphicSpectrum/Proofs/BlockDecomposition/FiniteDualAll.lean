import Mathlib

namespace GlobalTheory.CompanionTheory.DualFin

theorem finite_dual_all : ∀ (R M : Type) [CommRing R] [Finite R] [AddCommGroup M] [Module R M] [Finite M], Finite (Module.Dual R M) :=
  fun R M _ _ _ _ _ =>
    Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

end GlobalTheory.CompanionTheory.DualFin
