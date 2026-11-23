import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {E : Type} [Field E] {a b : ℕ}

def conjH (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[E] HomE E a b where
  toFun y := γ'.toLinearMap ∘ₗ y ∘ₗ γ.symm.toLinearMap
  invFun y := γ'.symm.toLinearMap ∘ₗ y ∘ₗ γ.toLinearMap
  map_add' y y' := by ext v i; simp
  map_smul' r y := by ext v i; simp
  left_inv y := by ext v i; simp
  right_inv y := by ext v i; simp

theorem conjH_symm_apply (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (y : HomE E a b) :
    (conjH γ γ').symm y = γ'.symm.toLinearMap ∘ₗ y ∘ₗ γ.toLinearMap := rfl

end Formalism.L2.Ker.TI
