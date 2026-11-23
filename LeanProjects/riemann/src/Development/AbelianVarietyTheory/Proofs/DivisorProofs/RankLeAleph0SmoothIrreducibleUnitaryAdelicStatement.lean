import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.FinTyp.rank_le_aleph0 | exact GlobalTheory.FinTyp.rank_le_aleph0 | (intros; apply GlobalTheory.FinTyp.rank_le_aleph0 <;> assumption)
