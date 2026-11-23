import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFraction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
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
theorem _root_.GlobalTheory.T.affineOpen_to_functionField_injective_and_fraction : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  first | exact @GlobalTheory.GenFrac.injective_and_frac | exact GlobalTheory.GenFrac.injective_and_frac | (intros; apply GlobalTheory.GenFrac.injective_and_frac <;> assumption)
