import Mathlib

namespace ReciprocityTheory.Coh.PowerKernelFiltration

universe u

section Art

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

def kerPow (t : R) (m : ℕ) : Submodule R N := LinearMap.ker ((t ^ m) • (LinearMap.id : N →ₗ[R] N))

def layer (t : R) (P : Submodule R N) (m : ℕ) : Submodule R N :=
  (P ⊓ kerPow t (m + 1)).map ((t ^ m) • (LinearMap.id : N →ₗ[R] N))

end Art

section Card

end Card

end ReciprocityTheory.Coh.PowerKernelFiltration
