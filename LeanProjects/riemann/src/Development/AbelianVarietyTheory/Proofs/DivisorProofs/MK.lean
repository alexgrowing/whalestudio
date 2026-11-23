import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.HomMum

abbrev MK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

variable {S : Scheme.{0}}

def mφ (H₁ H₂ : Over S) [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂) :
    MK → ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) :=
  Sum.elim (fun I => (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr)
    (fun I => (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl)

def mε : MK → ℤ :=
  Sum.elim (fun I => (-1 : ℤ) ^ (2 - I.down.card)) (fun I => -((-1 : ℤ) ^ (2 - I.down.card)))

def IsNrm {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {a b : H₁ ⟶ H₂}
    {L₁ : LB H₁.left} {L₂ : LB H₂.left} (u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)) : Prop :=
  u.IsGen ∧ ∀ (y : (𝟙_ (Over S)).left) (J), Good (join L₁ L₂) y J →
    val u (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left y J = 1

end GlobalTheory.HomMum
