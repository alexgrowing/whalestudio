import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutGlobal.Statement : Prop :=
  ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
    IsNilpotent P → IsPrincipalIdealRing (C ⧸ P) → y ∉ P → (P ⊔ Ideal.span {y}).IsMaximal →
      (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (M ⧸ (Ideal.span {y} • ⊤ : Submodule C M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
