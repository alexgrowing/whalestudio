import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistHomModuleIso
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_hom_module_iso : ∀ (Y : Scheme.{0}) (F G : Y.Modules) (M : LB Y), Nonempty (twist (homMod F G) M ≅ homMod F (twist G M)) := by
  first | exact @GlobalTheory.TwistHomMod.nonempty_iso | exact GlobalTheory.TwistHomMod.nonempty_iso | (intros; apply GlobalTheory.TwistHomMod.nonempty_iso <;> assumption)
