import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardTwistHomDualIso
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
theorem _root_.GlobalTheory.T.pushforward_twist_hom_dual_iso : ∀ (X Y : Scheme.{0}) (ρ : Y ⟶ X) (E : X.Modules) (r : ℕ), IsVB E r → ∀ (M : LB Y), M.IsLB → Nonempty ((Scheme.Modules.pushforward ρ).obj (twist ((Scheme.Modules.pullback ρ).obj E) M) ≅ homMod (dual E) ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M))) ∧ Nonempty ((Scheme.Modules.pushforward ρ).obj (twist ((Scheme.Modules.pullback ρ).obj (dual E)) M) ≅ homMod E ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M))) := by
  first | exact @GlobalTheory.ProjFml.projection_formula | exact GlobalTheory.ProjFml.projection_formula | (intros; apply GlobalTheory.ProjFml.projection_formula <;> assumption)
