import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueOneZeroFirstFactor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_value_one_zero_first_factor : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → IsAbelianScheme A → ∀ (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) → ∀ (T : Over S) (y : T ⟶ A) (z : T.left) (J : (T.left ⟶ A.left) → L.ι), Good L z J → val u (lift (1 : T ⟶ A) y).left z J = 1 := by
  first | exact @GlobalTheory.RosZeroLeft.val_lift_one_left | exact GlobalTheory.RosZeroLeft.val_lift_one_left | (intros; apply GlobalTheory.RosZeroLeft.val_lift_one_left <;> assumption)
