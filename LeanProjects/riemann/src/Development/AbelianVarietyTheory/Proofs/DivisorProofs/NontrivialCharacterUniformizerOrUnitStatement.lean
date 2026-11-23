import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialCharacterUniformizerOrUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_character_uniformizer_or_unit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ), IsUnif ϖ → ν ≠ 1 → ν ϖ ≠ 1 ∨ ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
  first | exact @GlobalTheory.CharSplit.ne_one_unif_or_unit | exact GlobalTheory.CharSplit.ne_one_unif_or_unit | (intros; apply GlobalTheory.CharSplit.ne_one_unif_or_unit <;> assumption)
