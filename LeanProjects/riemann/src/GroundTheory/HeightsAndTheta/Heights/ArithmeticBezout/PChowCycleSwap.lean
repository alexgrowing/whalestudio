import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChowCycleSwap.proof : ChowCycleSwap.Statement := by
  intro F _ n k Z f hf τ
  obtain ⟨c, -, g, hg, rfl⟩ := hf
  have hex : ∀ W, ∃ d : F, W ∈ Z.support →
      d ^ 2 = 1 ∧ rename (Prod.map τ id) (g W) = C d * g W := by
    intro W
    by_cases hW : W ∈ Z.support
    · obtain ⟨d, hd2, hdg⟩ := chowFormSwap F n k W (g W) (hg W hW) τ
      exact ⟨d, fun _ => ⟨hd2, hdg⟩⟩
    · exact ⟨1, fun h => absurd h hW⟩
  choose d hd using hex
  refine ⟨∏ W ∈ Z.support, d W ^ Z W, ?_, ?_⟩
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun W hW => ?_
    rw [← pow_mul, mul_comm, pow_mul, (hd W hW).1, one_pow]
  · rw [map_mul, rename_C, map_prod]
    rw [Finset.prod_congr rfl fun W hW => by
      rw [map_pow, (hd W hW).2, mul_pow, ← C_pow]]
    rw [Finset.prod_mul_distrib, map_prod C]
    ring

end

end GroundTheory.Heights₂.Heights
