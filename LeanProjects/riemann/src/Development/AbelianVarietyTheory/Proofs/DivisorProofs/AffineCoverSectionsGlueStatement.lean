import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineCoverSectionsGlue
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_sections_glue : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ m : ∀ i, D.M (W i) (hW i), (∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j), D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) → ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i := by
  first | exact @GlobalTheory.AffGlue.Cech.exists_glue | exact GlobalTheory.AffGlue.Cech.exists_glue | (intros; apply GlobalTheory.AffGlue.Cech.exists_glue <;> assumption)
