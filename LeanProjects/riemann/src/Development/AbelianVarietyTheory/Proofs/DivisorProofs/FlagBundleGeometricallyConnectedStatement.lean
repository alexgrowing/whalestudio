import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGeometricallyConnected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_geometrically_connected : ∀ (F : Type) [Field F] (G : Scheme.{0}) (s : G ⟶ Sp F) (ι : Type) [Fintype ι] (E : ι → (Sp F).Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → IsFlagBundle s E r fl → GeometricallyConnected s := by
  first | exact @GlobalTheory.FlagOverField.geometricallyConnected_of_isFlagBundle | exact GlobalTheory.FlagOverField.geometricallyConnected_of_isFlagBundle | (intros; apply GlobalTheory.FlagOverField.geometricallyConnected_of_isFlagBundle <;> assumption)
