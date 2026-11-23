import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointOfBoxProjections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.rosati_adjoint_of_box_projections : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (j : ℕ) (p : IsPowGrp A' A j) (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (w : LB.Iso L' (boxLB L p.pr)), w.IsGen → ∀ (f g : A ⟶ A) (f' g' : A' ⟶ A') (i l : Fin j), (∀ s, f' ≫ p.pr s = if s = i then p.pr l ≫ f else 1) → (∀ s, g' ≫ p.pr s = if s = l then p.pr i ≫ g else 1) → RosatiAdj A L f g → RosatiAdj A' L' f' g' := by
  first | exact @GlobalTheory.rosatiAdj_elementary | exact GlobalTheory.rosatiAdj_elementary | (intros; apply GlobalTheory.rosatiAdj_elementary <;> assumption)
