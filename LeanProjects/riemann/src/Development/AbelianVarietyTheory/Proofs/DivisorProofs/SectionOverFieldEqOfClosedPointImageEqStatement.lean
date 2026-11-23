import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_over_field_eq_of_closedPoint_image_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  first | exact @GlobalTheory.section_eq_of_point_eq | exact GlobalTheory.section_eq_of_point_eq | (intros; apply GlobalTheory.section_eq_of_point_eq <;> assumption)
