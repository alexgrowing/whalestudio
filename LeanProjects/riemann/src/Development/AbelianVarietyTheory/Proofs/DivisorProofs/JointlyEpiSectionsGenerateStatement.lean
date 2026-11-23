import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointlyEpiSectionsGenerate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointly_epi_sections_generate : ∀ (T : Scheme.{0}) (L Q : T.Modules) (N : ℕ) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s := by
  first | exact @GlobalTheory.LineQuot.gen_of_jointEpi | exact GlobalTheory.LineQuot.gen_of_jointEpi | (intros; apply GlobalTheory.LineQuot.gen_of_jointEpi <;> assumption)
