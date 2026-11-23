import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.PageSupportRows
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FourthHypothesisOfParams

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.RunJoin.Inh
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin GlobalTheory.Survey.NumericBoundConstants

theorem nums {A k b s PP TO rd r d q fm : ℝ} (h : Bs A k b s PP TO rd) (hr0 : 0 ≤ r) (hr : r ≤ A) (hd0 : 0 ≤ d)
    (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) (hf0 : 0 ≤ fm) (hf : fm ≤ k ^ 4) :
    (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ q ∧ TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 ≤ q ∧
      2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ q := by
  have hs : (10 : ℝ) ^ 100 ≤ s := h.sb_ge
  have hs1 : (40000 : ℝ) ≤ s := le_trans (by norm_num) hs
  have hk : (1 : ℝ) ≤ k := by linarith [h.k8]
  have hR : rd ^ 7 ≤ s := h.rd_pow_le (by norm_num)
  have hR0 : 0 ≤ rd ^ 7 := by have := h.rd1; positivity
  have hP0 : 0 ≤ PP := le_trans (by positivity) h.PP_ge
  have hP := h.PP_le_sb
  have hP3 := h.param_cube_le_bound
  have hTP := h.hTP
  have hT0 : 0 ≤ TO := by linarith [h.one_le_order_alt]
  have hb : b = s ^ 2 := by rw [← h.sb_sq]; ring
  have hd' : d ≤ 4 * k ^ 2 * s ^ 2 := by
    have := h.Ak
    rw [hb] at hd
    have : A * s ^ 2 ≤ 2 * k ^ 2 * s ^ 2 := by gcongr
    linarith
  have hq' : k ^ 8 * s ^ 16 ≤ q := by rw [hb] at hq; calc k ^ 8 * s ^ 16 = (k * s ^ 2) ^ 8 := by ring
    _ ≤ q := hq
  have hr' : r ≤ 2 * k ^ 2 := hr.trans h.Ak
  have key : ∀ (a c : ℕ) (C : ℝ), a ≤ 8 → c ≤ 15 → 0 ≤ C → C ≤ 40000 → C * (k ^ a * s ^ c) ≤ q := by
    intro a c C ha hc hC0 hC
    have e1 : k ^ a ≤ k ^ 8 := pow_le_pow_right₀ hk ha
    have e2 : s ^ c ≤ s ^ 15 := pow_le_pow_right₀ (by linarith) hc
    calc C * (k ^ a * s ^ c) ≤ s * (k ^ 8 * s ^ 15) := by gcongr; linarith
      _ = k ^ 8 * s ^ 16 := by ring
      _ ≤ q := hq'
  refine ⟨?_, ?_, ?_⟩
  · calc (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ s ^ 4 * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 16 * (k ^ 4 * s ^ 9) := by ring
      _ ≤ q := key 4 9 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 = (TO * PP) * (1250 * r) * rd ^ 7 * d ^ 2 := by ring
      _ ≤ s * (1250 * (2 * k ^ 2)) * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 40000 * (k ^ 6 * s ^ 6) := by ring
      _ ≤ q := key 6 6 40000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc 2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ 2 * (k ^ 4 * s ^ 2 * (s * s * (4 * k ^ 2 * s ^ 2) ^ 2)) := by gcongr
      _ = 32 * (k ^ 8 * s ^ 8) := by ring
      _ ≤ q := key 8 8 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem eRR7 : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
  unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7

end GlobalTheory.RunJoin.Inh
