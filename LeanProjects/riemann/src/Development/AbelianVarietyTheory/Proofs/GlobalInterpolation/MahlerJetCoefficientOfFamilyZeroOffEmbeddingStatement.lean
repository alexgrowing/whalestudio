import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) → (∀ p, p ∉ Set.range e → u p = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧ (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  first | exact @GlobalTheory.MomEmbed.mahler_embed | exact GlobalTheory.MomEmbed.mahler_embed | (intros; apply GlobalTheory.MomEmbed.mahler_embed <;> assumption)
