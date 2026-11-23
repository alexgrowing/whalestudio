import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAt
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineFunction_weighted_translates_unitAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by
  first | exact @GlobalTheory.CharIndepAt.main | exact GlobalTheory.CharIndepAt.main | (intros; apply GlobalTheory.CharIndepAt.main <;> assumption)
