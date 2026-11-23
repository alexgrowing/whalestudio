import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRoots
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ ι : On p m →ₐ[O0 p] Ω, IsEmb T m ι →
  Function.Injective ι ∧ ι.range = Lev T m := by
  first | exact @GlobalTheory.K5.LevEmb.emb_inj_range | exact GlobalTheory.K5.LevEmb.emb_inj_range | (intros; apply GlobalTheory.K5.LevEmb.emb_inj_range <;> assumption)
