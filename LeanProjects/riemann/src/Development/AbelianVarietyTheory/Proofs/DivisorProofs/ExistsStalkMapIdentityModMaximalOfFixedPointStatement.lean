import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkMapIdentityModMaximalOfFixedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_map_identity_mod_maximal_of_fixed_point : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  first | exact @GlobalTheory.FixStalk.fixes_stalk | exact GlobalTheory.FixStalk.fixes_stalk | (intros; apply GlobalTheory.FixStalk.fixes_stalk <;> assumption)
