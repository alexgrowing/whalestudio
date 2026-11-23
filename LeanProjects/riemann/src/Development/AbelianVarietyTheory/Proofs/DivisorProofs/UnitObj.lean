import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F]

def unitObj (𝔠 : FracId F) (n : ℕ) : ObjClass 𝔠 := fun R _ _ ↦ IsUnit (n : R)

def levObj (𝔠 : FracId F) (N : ℕ) : ObjClass 𝔠 := fun R _ X ↦ IsUnit (N : R) ∧ Nonempty (X.Level N)

end GlobalTheory.RealMult
