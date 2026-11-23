import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_relation_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s → Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  first | exact @GlobalTheory.LineQuot.rel_pullback | exact GlobalTheory.LineQuot.rel_pullback | (intros; apply GlobalTheory.LineQuot.rel_pullback <;> assumption)
