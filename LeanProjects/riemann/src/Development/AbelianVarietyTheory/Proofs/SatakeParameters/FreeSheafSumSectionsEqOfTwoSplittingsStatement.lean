import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeSheafSumSectionsEqOfTwoSplittings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → GlobalTheory.EtC.Tr.SplitBy f y s' → ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  first | (exact @GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (exact GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (intros; apply GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings  <;> assumption)
