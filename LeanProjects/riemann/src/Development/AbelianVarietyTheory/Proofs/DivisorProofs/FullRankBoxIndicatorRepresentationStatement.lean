import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankBoxIndicatorRepresentation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_box_indicator_representation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ d : ℕ) (T : Type) [Fintype T] [DecidableEq T] (b : kˣ), ∀ θ ∈ fullRk k ρ d,
    ∃ Θ ∈ SB (Matrix (Fin ρ ⊕ T) (Fin d) k), ∀ Y : Matrix (Fin ρ ⊕ T) (Fin d) k, Y.rank ≤ ρ →
      Θ Y = Set.indicator {Z : Matrix (Fin ρ ⊕ T) (Fin d) k | ∃ C ∈ GlobalTheory.LocMod.Inhab.box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁}
        (fun Z => θ Z.toRows₁) Y := by
  first | exact @GlobalTheory.RankChart.Extend.exists_sb_extension | exact GlobalTheory.RankChart.Extend.exists_sb_extension | (intros; apply GlobalTheory.RankChart.Extend.exists_sb_extension <;> assumption)
