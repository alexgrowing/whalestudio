import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.H1cEqH1

namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [Ring R] {A B C D : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

theorem length_add_of_exact₄ (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) :
    Module.length R A + Module.length R C = Module.length R B + Module.length R D := by
  have h1 : Module.length R B = Module.length R A + Module.length R (LinearMap.range g) := by
    refine Module.length_eq_add_of_exact f g.rangeRestrict hf g.surjective_rangeRestrict ?_
    intro x
    rw [← hfg x]
    exact Subtype.ext_iff
  have h2 : Module.length R C = Module.length R (LinearMap.range g) + Module.length R D := by
    refine Module.length_eq_add_of_exact (LinearMap.range g).subtype h
      (Submodule.injective_subtype _) hh ?_
    intro x
    rw [hgh x]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  rw [h1, h2, add_assoc]

theorem length_eq_of_exact₄ (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) (hAD : Module.length R A = Module.length R D)
    (hfin : Module.length R A ≠ ⊤) : Module.length R B = Module.length R C := by
  have h1 := length_add_of_exact₄ f g h hf hfg hgh hh
  rw [← hAD, add_comm (Module.length R B)] at h1
  exact (ENat.add_right_injective_of_ne_top hfin h1).symm

theorem length_ker_eq_length_coker (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (LinearMap.ker f) = Module.length R (A ⧸ LinearMap.range f) := by
  have h1 := length_add_of_exact₄ (LinearMap.ker f).subtype f (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map f)
    (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)
  rw [add_comm (Module.length R (LinearMap.ker f))] at h1
  exact ENat.add_right_injective_of_ne_top hfin h1

end KStar.Selmer
