import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniqueOfRelation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_map_unique_of_relation : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (φ ψ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Gen s → φ ≫ PSpace.str k N = ψ ≫ PSpace.str k N → Rel φ s → Rel ψ s → φ = ψ := by
  first | exact @GlobalTheory.LineQuot.eq_of_rel | exact GlobalTheory.LineQuot.eq_of_rel | (intros; apply GlobalTheory.LineQuot.eq_of_rel <;> assumption)
