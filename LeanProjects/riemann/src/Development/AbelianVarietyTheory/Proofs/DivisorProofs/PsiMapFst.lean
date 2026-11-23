import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

def psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) : A ⊗ A ⟶ A ⊗ A :=
  lift (fst A A ^ a₁ * snd A A ^ b₁) (fst A A ^ a₂ * snd A A ^ b₂)

theorem psiMap_fst {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ fst A A = fst A A ^ a₁ * snd A A ^ b₁ := lift_fst _ _

theorem psiMap_snd {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ snd A A = fst A A ^ a₂ * snd A A ^ b₂ := lift_snd _ _

end GlobalTheory.AmpleGen
