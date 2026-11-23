import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
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
theorem _root_.GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  first | exact @GlobalTheory.NumPull.interNumRed_pull_proportional | exact GlobalTheory.NumPull.interNumRed_pull_proportional | (intros; apply GlobalTheory.NumPull.interNumRed_pull_proportional <;> assumption)
