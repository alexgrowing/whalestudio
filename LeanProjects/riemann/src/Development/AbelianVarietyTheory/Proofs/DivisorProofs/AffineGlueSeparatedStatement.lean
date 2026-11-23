import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineGlueSeparated
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_glue_separated : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by
  first | exact @GlobalTheory.AffGlue.eq_zero_of_cover_zero | exact GlobalTheory.AffGlue.eq_zero_of_cover_zero | (intros; apply GlobalTheory.AffGlue.eq_zero_of_cover_zero <;> assumption)
