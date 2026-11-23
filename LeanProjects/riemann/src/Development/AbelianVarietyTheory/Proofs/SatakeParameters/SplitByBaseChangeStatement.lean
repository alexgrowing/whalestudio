import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitByBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitBy_baseChange' : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  first | (exact @GlobalTheory.EtC.Tr.splitBy_baseChange) | (exact GlobalTheory.EtC.Tr.splitBy_baseChange) | (intros; apply GlobalTheory.EtC.Tr.splitBy_baseChange  <;> assumption)
