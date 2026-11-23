import Mathlib

namespace PI

def CharExtend : Prop :=
  ∀ (G : Type) [CommGroup G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ ψ : G →* ℂˣ, ∀ h : H, ψ (h : G) = χ h

end PI
