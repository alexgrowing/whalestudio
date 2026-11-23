import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingSectionsProjectiveMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generating_sections_projective_map : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (f : T ⟶ Sp k) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → Gen s → ∃ φ : T ⟶ PSpace k N, φ ≫ PSpace.str k N = f ∧ Rel φ s := by
  first | exact @GlobalTheory.LineQuot.exists_toPSpace | exact GlobalTheory.LineQuot.exists_toPSpace | (intros; apply GlobalTheory.LineQuot.exists_toPSpace <;> assumption)
