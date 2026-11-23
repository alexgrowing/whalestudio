import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreOfEtaleRestriction
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
theorem _root_.GlobalTheory.T.isolated_in_fibre_of_etale_restriction : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : W.Opens), Etale (f ∣_ U) → ∀ z : M, f z ∈ U → ∃ V : M.Opens, z ∈ V ∧ ∀ y ∈ V, f y = f z → y = z := by
  first | exact @GlobalTheory.isolated_in_fibre_of_etale_restrict | exact GlobalTheory.isolated_in_fibre_of_etale_restrict | (intros; apply GlobalTheory.isolated_in_fibre_of_etale_restrict <;> assumption)
