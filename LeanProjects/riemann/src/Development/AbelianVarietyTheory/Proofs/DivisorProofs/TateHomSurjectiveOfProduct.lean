import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonObj GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped TensorProduct

namespace GlobalTheory.AV.ProdRed

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def inl (A B : AbVar K) : A ⟶ prod A B := prodLift (𝟙 A) 0

def inr (A B : AbVar K) : B ⟶ prod A B := prodLift 0 (𝟙 B)

def restr (A B : AbVar K) : (prod A B ⟶ prod A B) →ₗ[ℤ] (A ⟶ B) :=
  (AddMonoidHom.mk' (fun f => inl A B ≫ f ≫ prodSnd A B) fun f g => by
    simp only [Preadditive.add_comp, Preadditive.comp_add]).toIntLinearMap

end GlobalTheory.AV.ProdRed
