import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutCaseDecomp.proof (h₁ : RestCutRestHom.Statement) (h₂ : RestCutHomDecomp.Statement)
    (h₃ : RestCutTransportPsum.Statement) : RestCutCaseDecomp.Statement := by
  rintro f j k r a cs e hf hN h2 hF ⟨Q₀, hQ₀⟩
  have hD : flagDim f j k = RestTerms.topDegree f (r + a) := by
    simp only [flagDim, RestTerms.topDegree, hN]
  have hFh := (h₁ f r a cs).2
  have hND : r + a ≤ RestTerms.topDegree f (r + a) + 1 := by
    have h1 : (r + a - 1) * 2 ≤ (r + a) * (r + a - 1) := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ h2
    have h2' : r + a - 1 ≤ (r + a) * (r + a - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
    have h3 : (r + a) * (r + a - 1) / 2 ≤ RestTerms.topDegree f (r + a) := by
      unfold RestTerms.topDegree; exact Nat.le_mul_of_pos_left _ hf
    omega
  have hdec := h₂ f (r + a) _ Q₀ _ hQ₀ hFh hND
  refine ⟨⟨_, hdec, fun l σ _ _ => ?_⟩, ?_⟩
  · rw [hD]; exact homogeneousComponent_isHomogeneous _ _
  refine ⟨fun τ m => restTransport f j k (r + a) e
    (homogeneousComponent (RestTerms.topDegree f (r + a) + 1 - m) (Q₀ m τ)), fun τ m _ _ => ?_, ?_⟩
  · show (restRename f j k (r + a) e (map (algebraMap ℚ ℝ) _)).IsHomogeneous _
    rw [hD]
    exact ((homogeneousComponent_isHomogeneous _ _).map _).rename_isHomogeneous
  · rw [← hF]
    conv_lhs => rw [hdec]
    rw [map_sum, Finset.sum_comm, ← hN]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, h₃]

end GroundTheory.Heights₂.Heights
