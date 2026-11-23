import Mathlib

namespace Formalism.KernelCokernelLengths

def KerCokerEq : Prop :=
  ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
    ∀ f : Module.End O M, Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f)

def CokerSurj : Prop :=
  ∀ (O : Type) [CommRing O] (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M']
    [Module O M'] (f : Module.End O M) (f' : Module.End O M') (g : M →ₗ[O] M'),
    Function.Surjective g → g ∘ₗ f = f' ∘ₗ g →
      Module.length O (M' ⧸ LinearMap.range f') ≤ Module.length O (M ⧸ LinearMap.range f)

end Formalism.KernelCokernelLengths
