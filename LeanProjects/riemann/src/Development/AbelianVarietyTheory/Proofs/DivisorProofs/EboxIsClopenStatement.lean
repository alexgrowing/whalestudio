import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EboxIsClopen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ebox_isClopen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [Fintype D] (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ), IsClopen (ebox ϖ C r) := by
  first | exact @GlobalTheory.NormalCore.isClopen_ebox | exact GlobalTheory.NormalCore.isClopen_ebox | (intros; apply GlobalTheory.NormalCore.isClopen_ebox <;> assumption)
