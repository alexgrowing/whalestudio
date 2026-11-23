import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOpenConditions
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationOverZpHolds
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundOfDualFamilies
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.EpsilonBoundMConstant

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thresholds_mono_normalized {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 1 ≤ C0 → 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  unfold Formalism.MainNotions.flipOneThree.TransportedAlt at hP ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨max T0 1, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 (le_trans (le_max_left _ _) hC0)
  refine ⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 hE1 hE2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb hY hde hk hD hb => ?_⟩
  have hT2' : T2 ≤ max T2 2 := le_max_left _ _
  have h2' : (2 : ℝ) ≤ max T2 2 := le_max_right _ _
  have h1' : (1 : ℝ) ≤ max T0 1 := le_max_right _ _
  exact h C0 CYb Cde Ck CD Cb CE1 CE2 Cc (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (hT2'.trans hY) (hT2'.trans hde) (hT2'.trans hk) (hT2'.trans hD) (hT2'.trans hb))

def RestOpen4 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusA C0 CE1 CE2 X CM ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpen4E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen4 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem openE_of_open4 (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : RestOpenE D := by
  obtain ⟨CM, hCM, hTM⟩ := restTM_closed
  exact thresholds_mono_normalized (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hC0 hY hD hb h1 h2 hP Ckap Cs =>
    ⟨CM, by linarith, fun X hA hH => by
      obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
      have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
      exact ⟨block_bound_of_dual_families C0 CE1 CE2 X (block_valuation_over_Zp_holds C0 CE1 CE2 X (by linarith) h1 h2 hH) a,
        restPlus_of CM hY0 b (restRankL_proved C0 CE1 CE2 X) c,
        hTM D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hY hb hD hC0 h1 h2 hH, d⟩⟩) h

theorem closed_of_open_directions (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_conditions D (openE_of_open4 D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
