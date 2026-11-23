import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RosAddPair

open GlobalTheory.TauBalAdd

theorem ros_val_padd : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (cu : CubicalStr A Lr), GlobalFnsSt →
    IsAbelianScheme A →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = padd A f₁ f₂ → g = padd A g₁ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₂ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → Lr.L.ι}, Good Lr.L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y * cubV cu z J (y ≫ g₁) (y ≫ g₂) x =
      cubV cu z J (x ≫ f₁) (x ≫ f₂) y * (val₂ u₁ z J x y * val₂ u₂ z J x y) := by
  intro S A _ _ Lr cu hG hA f₁ g₁ f₂ g₂ f g _ _ _ _ hf hg u₁ u₂ u hu₁ hu₂ hu h₁ h₂ h₀ T z J hJ x y
  subst hf hg
  have key := ros_sum cu hG hA f₁ g₁ f₂ g₂ u₁ hu₁ h₁ u₂ hu₂ h₂ u hu h₀ hJ x y
  have C : IsCub (cubV cu z J) := isCub_cubV cu hJ
  rw [C.s01 x, C.s12 _ x] at key
  exact key

end GlobalTheory.RosAddPair
