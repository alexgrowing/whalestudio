import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift
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
theorem _root_.GlobalTheory.T.rosati_adjoint_balanced_power_lift : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → ∀ (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g] (a b : D.X → D.X), (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → RosatiAdj D.P.A D.P.L f g → D.TauBal f g a b → ∀ (f' g' : D'.P.A ⟶ D'.P.A) (i l : Fin j), (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → (∀ s, g' ≫ pD.pw.pr s = if s = l then pD.pw.pr i ≫ g else 1) → D'.TauBal f' g' (fun y => pD.xe.symm (Pi.single i (a (pD.xe y l)))) (fun y => pD.xe.symm (Pi.single l (b (pD.xe y i)))) := by
  first | exact @GlobalTheory.TauBalElem.tauBal_elem | exact GlobalTheory.TauBalElem.tauBal_elem | (intros; apply GlobalTheory.TauBalElem.tauBal_elem <;> assumption)
