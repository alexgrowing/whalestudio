import Mathlib

open TensorProduct

namespace PI.CoefExt

def InvBaseChange : Prop :=
  ∀ (LL LL' : Type) [Field LL] [Field LL'] [Algebra LL LL'] (W : Type) [AddCommGroup W] [Module LL W]
    (G : Type) (T : G → W →ₗ[LL] W),
    Module.finrank LL' (⨅ g, LinearMap.ker ((T g).baseChange LL' - LinearMap.id) : Submodule LL' (LL' ⊗[LL] W))
      = Module.finrank LL (⨅ g, LinearMap.ker (T g - LinearMap.id) : Submodule LL W)

end PI.CoefExt
