import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_preserves_line_bundle_flag : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (E : X.Modules) (l : List (LB X)), HasFlag E l → HasFlag ((Scheme.Modules.pullback f).obj E) (l.map fun L => L.pull f) := by
  first | exact @GlobalTheory.FlagPull.hasFlag_pullback | exact GlobalTheory.FlagPull.hasFlag_pullback | (intros; apply GlobalTheory.FlagPull.hasFlag_pullback <;> assumption)
