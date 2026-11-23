import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) → IsHilbRep z r := by
  first | (exact @GlobalTheory.HilbGlue.isHilbRep_of_cover) | (exact GlobalTheory.HilbGlue.isHilbRep_of_cover) | (intros; apply GlobalTheory.HilbGlue.isHilbRep_of_cover <;> assumption)
