import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

noncomputable section

namespace GlobalTheory.BalRank

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

def balBil : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β β' h k a y z
    simp only [LinearMap.add_apply, h a y z, k a y z]
  zero_mem' := by simp
  smul_mem' := by
    rintro n β h a y z
    simp only [LinearMap.smul_apply, h a y z]

variable {bar X}

end GlobalTheory.BalRank
