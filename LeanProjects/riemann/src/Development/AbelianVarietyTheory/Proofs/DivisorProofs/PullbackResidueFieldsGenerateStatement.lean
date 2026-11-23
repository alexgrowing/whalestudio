import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_residue_fields_generate : ∀ (X Y S : AlgebraicGeometry.Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S) (t : ↑(CategoryTheory.Limits.pullback f g)), Subfield.closure (Set.range ((CategoryTheory.Limits.pullback.fst f g).residueFieldMap t).hom ∪ Set.range ((CategoryTheory.Limits.pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  first | exact @GlobalTheory.closure_range_residueFieldMap_pullback_eq_top | exact GlobalTheory.closure_range_residueFieldMap_pullback_eq_top | (intros; apply GlobalTheory.closure_range_residueFieldMap_pullback_eq_top <;> assumption)
