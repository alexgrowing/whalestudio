import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSurfacePullbackLaw
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_surface_pullback_law : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → PullbackLaw k T := by
  first | exact @GlobalTheory.PullCh.pullbackLaw | exact GlobalTheory.PullCh.pullbackLaw | (intros; apply GlobalTheory.PullCh.pullbackLaw <;> assumption)
