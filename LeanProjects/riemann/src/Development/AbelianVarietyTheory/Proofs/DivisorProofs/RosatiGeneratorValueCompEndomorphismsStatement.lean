import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueCompEndomorphisms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_value_comp_endomorphisms : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}, GlobalFnsSt → IsAbelianScheme A → L.IsLB →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = f₂ ≫ f₁ → g = g₁ ≫ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.ι}, Good L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y = val₂ u₁ z J (x ≫ f₂) y * val₂ u₂ z J x (y ≫ g₁) := by
  first | exact @GlobalTheory.rosGen_comp_val | exact GlobalTheory.rosGen_comp_val | (intros; apply GlobalTheory.rosGen_comp_val <;> assumption)
