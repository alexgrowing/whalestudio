import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem RestTermSharp.proof (h₁ : RestCutCaseSharp.Statement)
    (h₂ : RestCutTransportLast.Statement) (h₃ : RestCutTransportFirst.Statement)
    (h₄ : RestCutLieLast.Statement) (h₅ : RestCutLieFirst.Statement) :
    RestTermSharp.Statement := by
  intro f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  by_cases hkj : k ≤ j
  · obtain ⟨hF, hJ⟩ := h₂ f j k hkj
    exact h₁ f j k k j .last (restLastEquiv j k) hf hj hk hk hj (Nat.add_comm k j)
      (Nat.mul_comm k j) hF hJ (h₄ f j k hkj) I hI vol hvol P hP B₀ hB φ
  · have hjk : j < k := by omega
    obtain ⟨hF, hJ⟩ := h₃ f j k hjk
    exact h₁ f j k j k .first (restFirstEquiv j k) hf hj hk hj hk rfl rfl hF hJ (h₅ f j k hjk)
      I hI vol hvol P hP B₀ hB φ

theorem RestTerm.proof (h : RestTermSharp.Statement) : RestTerm.Statement := by
  refine ⟨1.6, by norm_num, ?_⟩
  intro f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  obtain ⟨hex, hall⟩ := h f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  refine ⟨hex, fun Q hQ => ?_⟩
  obtain ⟨hs, hb⟩ := hall Q hQ
  refine ⟨hs, hb.trans ?_⟩
  have hmin : (1 : ℝ) ≤ ((min j k : ℕ) : ℝ) := by exact_mod_cast le_min hj hk
  have hnn : 0 ≤ (((f * j * k : ℕ) : ℝ) + 1) * vol * |I (degreeInput f j k)| := by positivity
  have := mul_nonneg (sub_nonneg.2 hmin) hnn
  nlinarith

end GroundTheory.Heights₂.Heights
