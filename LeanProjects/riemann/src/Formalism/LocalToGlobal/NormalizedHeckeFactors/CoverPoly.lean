import Mathlib

namespace Formalism.L2.NCov

open Module

variable {K₁ K₂ V₁ V₂ : Type*} [Field K₁] [Field K₂] [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂]
  [Module K₂ V₂]

theorem repr_transport (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (x : V₁) (r : n) :
    (Module.Basis.mk hli hsp.ge).repr (ι x) r = σ (b.repr x r) := by
  have hx : ι x = ∑ i, σ (b.repr x i) • (Module.Basis.mk hli hsp.ge) i := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.mk_apply, Function.comp_apply]
    first
      | exact LinearMap.map_smulₛₗ ι (b.repr x i) (b i)
      | exact map_smulₛₗ ι (b.repr x i) (b i)
      | simp
  rw [hx, Module.Basis.repr_sum_self]

theorem charpoly_transport_basis [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ a, A₂ (ι (b a)) = ι (A₁ (b a))) :
    A₂.charpoly = A₁.charpoly.map σ := by
  have hM : LinearMap.toMatrix (Module.Basis.mk hli hsp.ge) (Module.Basis.mk hli hsp.ge) A₂ =
      (LinearMap.toMatrix b b A₁).map σ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Module.Basis.mk_apply, Function.comp_apply, h j, repr_transport σ ι b hli hsp]
  rw [← LinearMap.charpoly_toMatrix A₂ (Module.Basis.mk hli hsp.ge), hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

theorem charpoly_transport [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ x, A₂ (ι x) = ι (A₁ x)) :
    A₂.charpoly = A₁.charpoly.map σ :=
  charpoly_transport_basis σ ι b hli hsp A₁ A₂ fun a => h (b a)

end Formalism.L2.NCov
