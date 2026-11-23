import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoByTwo

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def inl (A : AbVar K) : A ⟶ prod A A := prodLift (𝟙 A) 0

def inr (A : AbVar K) : A ⟶ prod A A := prodLift 0 (𝟙 A)

end GlobalTheory.TwoByTwo

namespace GlobalTheory.TwoByTwo

end GlobalTheory.TwoByTwo
