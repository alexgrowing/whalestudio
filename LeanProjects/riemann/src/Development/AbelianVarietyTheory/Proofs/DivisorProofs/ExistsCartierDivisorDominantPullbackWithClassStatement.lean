import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
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
theorem _root_.GlobalTheory.T.exists_cartierDivisor_dominant_pullback_with_class : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ] (D : CartierDiv X), ∃ D' : CartierDiv X', cls (toLB D') (isLB_toLB D') = cls ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) ∧ ∀ (x : X') (g : X.functionFieldˣ), D.IsEqn (φ x) g → D'.IsEqn x (Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom g) := by
  first | exact @GlobalTheory.Cartier.exists_pullback_cartierDiv | exact GlobalTheory.Cartier.exists_pullback_cartierDiv | (intros; apply GlobalTheory.Cartier.exists_pullback_cartierDiv <;> assumption)
