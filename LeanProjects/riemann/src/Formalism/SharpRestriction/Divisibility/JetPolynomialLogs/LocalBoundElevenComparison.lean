import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.UniformBoundAllData
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LogbAddOneNonneg
import Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.product_zeroth_first_parts

open Formalism.BasicNotions

def Loc.Cor2 (L : Loc) (C6 Cd : ℝ) : Prop :=
  ∀ a : ℝ, L.HidaSetting a →
    ∀ (k : ℕ) (w E : ZMod L.d → ℝ), 3 ≤ k → (∀ s, 0 < w s) →
      (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ L.TT → (L.Dl s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ L.TT → (L.Dl s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      KvalGe L.N0 L.N1 L.l L.nu L.Th
        ((∑ s ∈ L.TT, L.baseTerm s) + lpF L.l L.d (fun s => ((k : ℝ) - 1) * w s) -
          C6 * (∑ s, w s) / (L.l : ℝ) - gam L.l * (∑ s ∈ L.TT, (L.Wc s : ℝ)) -
          Cd * ((L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1)))

def SplitConstantsUniformBound (C6 Cd : ℝ) : Prop :=
  (∀ L : Loc, L.AdmB → L.ThmA Cd ∧ L.Cor2 C6 Cd) ∧ ∀ L : Loc1, L.AdmB → L.ThmOne Cd

end Formalism.MainNotions.product_zeroth_first_parts

namespace Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights

open Formalism.MainNotions Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel

theorem local_bound_eleven_comparison (L : product_zeroth_first_parts.Loc) (k : ℕ) (w E : ZMod L.d → ℝ) (hk : 3 ≤ k) (hw : ∀ s, 0 < w s)
    (hE : ∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s)
    (hD1 : ∀ s, s ∉ L.TT → (L.Dl s : ℝ) = ((k : ℝ) - 1) * w s + E s)
    (hD2 : ∀ s, s ∈ L.TT → (L.Dl s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) :
    Formalism.BasicNotions.lpF L.l L.d (fun s => ((k : ℝ) - 1) * w s) - 11 * (∑ s, w s) / (L.l : ℝ) ≤ L.FD := by
  have h3 : 3 ≤ L.l := (by norm_num : 3 ≤ 5).trans L.J.five_le_l
  have key := Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.normCor7 L.l L.d h3 L.J.two_le_d L.J.d_even L.TT (fun _ => 0) (fun _ => 0)
    (fun s => L.Dl s) k 0 w E (1 / 2) _ (by norm_num) (by norm_num) hk hw hE
    (fun s hs => by simp only [Dl, if_neg hs]; exact hD1 s hs)
    (fun s hs => by simp only [Dl, if_pos hs, Nat.sub_zero]; exact hD2 s hs) le_rfl
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)] at key
  simp only [top0, zero_sub, Dl, Nat.sub_zero, ite_self, sub_zero, ← lpF_eq_Fnum,
    Finset.sum_neg_distrib] at key
  rw [Finset.mul_sum (s := L.TT)] at key
  have hg : 0 ≤ ∑ s ∈ L.TT, Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.oddLevelGainSum L.l L.d L.TT (fun _ => 0) (fun _ => 0) s :=
    Finset.sum_nonneg fun s _ => by
      unfold Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.oddLevelGainSum
      exact tsum_nonneg fun e => by
        split_ifs <;> first | exact le_max_right _ _ | exact le_rfl | positivity
  have h11 : 11 / (L.l : ℝ) * ∑ s, w s = 11 * (∑ s, w s) / (L.l : ℝ) := by ring
  unfold product_zeroth_first_parts.Loc.FD
  linarith

theorem corollary_split_eleven_one (hB : TieB) (hB0 : KernelFromExponentialTwist) (hF : TieFrame) (L : product_zeroth_first_parts.Loc) (hL : L.AdmB) : L.Cor2 11 1 := by
  intro a ha k w E hk hw hE hD1 hD2
  have hlp := local_bound_eleven_comparison L k w E hk hw hE hD1 hD2
  refine kval_mono (thmA_of hB hB0 hF L hL a ha) ?_
  have hg := Finset.sum_le_sum (s := L.TT) fun s _ => base_term_le_top_term L s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

theorem split_bound_eleven_one : product_zeroth_first_parts.SplitConstantsUniformBound 11 1 := by
  unfold product_zeroth_first_parts.SplitConstantsUniformBound
  exact ⟨fun L hL => ⟨thmA_of tieB kernel_from_twist_holds tieFrame L hL, corollary_split_eleven_one tieB kernel_from_twist_holds tieFrame L hL⟩,
    fun L hL => thmOne_of tieB kernel_twist_one_letter_holds tieFrameOne L hL⟩

end Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights

end
