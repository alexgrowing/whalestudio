import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFormallyUnramifiedOfEqAtClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint : ∀ {S T : Scheme.{0}} (f : T ⟶ S) [FormallyUnramified f]
    [LocallyOfFiniteType f] (R : CommRingCat.{0}) [IsLocalRing R] (u₁ u₂ : Spec R ⟶ T) (h : u₁ ≫ f = u₂ ≫ f)
    (K : Type) [Field K] (k : Sp K ⟶ Spec R) (hk : ∀ x, k x = IsLocalRing.closedPoint R)
    (hku : k ≫ u₁ = k ≫ u₂), u₁ = u₂ := by
  first | exact @GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint | exact GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint | (intros; apply GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint <;> assumption)
