import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLeStatement

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond

theorem thl_nonneg_leaf (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem err_mono_leaf (Cc C k m f w Se Se' th l T X : ℝ) (hCc : 0 < Cc) (hC : Cc ≤ C) (hk : 1 ≤ k) (hm : 1 ≤ m) (hf : 8 ≤ f)
    (hw : 0 ≤ w) (hS : Se' ≤ Se) (hS0 : 0 ≤ Se) (hth : 0 ≤ th) (hl : 0 ≤ l) :
    Cc * (Real.log k * m * w / l + f * k * Se' / l + k * th * w + if X < l then k * w / l ^ 2 else 0) ≤
      C * (Real.log k * m * w + f * k * Se) / l + C * k * w * th + T * 0 + if X < l then C * k * w / l ^ 2 else 0 := by
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk
  have hk0 : 0 ≤ k := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have h1 : f * k * Se' / l ≤ f * k * Se / l :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) hl
  have hI : 0 ≤ (if X < l then k * w / l ^ 2 else 0) := by split_ifs <;> positivity
  have hR : C * (Real.log k * m * w + f * k * Se) / l + C * k * w * th + T * 0 + (if X < l then C * k * w / l ^ 2 else 0) =
      C * (Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0) := by
    split_ifs <;> ring
  rw [hR]
  have h0 : 0 ≤ Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0 := by
    positivity
  calc _ ≤ Cc * (Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0) :=
        mul_le_mul_of_nonneg_left (by linarith) hCc.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hC h0

theorem leafGood : LeafGoodSt := by
  intro C1 hC1
  obtain ⟨Cc, hCc, hnu⟩ := GlobalTheory.T.goodPlaceDepthBound_proof C1 hC1
  refine ⟨max Cc 20, ?_⟩
  intro E _ _ _ H lv Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm N pl hC0 hE hσ hT hpr hsp hlev hstar hEx hPk hPl hj
    hN hPg tF tP
  have hCcC : Cc ≤ O.C := le_trans (le_max_left _ _) hC0
  have h20 : (20 : ℝ) ≤ O.C := le_trans (le_max_right _ _) hC0
  have hPg' := hPg
  obtain ⟨hC, hk, hm, hf, -, hSc, heta, -, -, -, pg1, pg2, -⟩ := hPg'
  have hb : 0 < O.b := Real.exp_pos _
  have hkN : 1 ≤ N.R.k := by
    have := hN.k_eq ▸ hk
    exact_mod_cast this
  refine ⟨fun l => ⟨?_, ?_⟩, fun Q hQ => ?_, fun Q _ => ?_, fun w _ hw j => ?_⟩
  · rw [hN.th_eq]; exact thl_nonneg_leaf _ _
  · rw [hN.ad_eq]
  · simp only [hN.th_eq]
    refine (GlobalTheory.T.sum_level_tail_mul_log_primes_le.2 N.R.k Q hkN hQ).trans ?_
    rw [hN.k_eq]
    exact div_le_div_of_nonneg_right h20 (Nat.cast_nonneg _)
  · simp only [hN.ad_eq, zero_mul, Finset.sum_const_zero, mul_zero]
    have : 0 ≤ O.m := by linarith
    have : 0 ≤ O.C := by linarith
    positivity
  · obtain ⟨j1, j2, jp, jq, jD, jG⟩ := hj j
    obtain ⟨t1, t2, t3, t4, t5⟩ := tP
    have hp : (Formalism.EigenvalueLevelCeiling.plc w).Prime := Formalism.EigenvalueLevelCeiling.plc_prime w
    have hw' := hw
    simp only [not_or] at hw'
    obtain ⟨n2, nq, nd, ng1, ng2⟩ := hw'
    have hF : Nm.F0 w j = N.FjP (ι j) (Formalism.EigenvalueLevelCeiling.plc w) := tF w j
    have key : ∀ v : HeightOneSpectrum (𝓞 K), Formalism.EigenvalueLevelCeiling.plc v = Formalism.EigenvalueLevelCeiling.plc w →
        O.e0 v j ≤ Nm.F0 w j + O.aE j (Formalism.EigenvalueLevelCeiling.plc w) + 1 ∧ (O.Y < (Formalism.EigenvalueLevelCeiling.plc w : ℝ) → O.e0 v j = 0) := by
      intro v hv
      have hr : resCharOf (placeBelow (K := c.F) v) = Formalism.EigenvalueLevelCeiling.plc w := (DepthTie.resChar_below (F := c.F) v).trans hv
      obtain ⟨e1, e2⟩ := GlobalTheory.T.onObj_exponent_eq_rounded_depth E H lv Dw Xo c Dd K Bs Df S P oc O ι hE hσ hpr hsp hPg v j (by rw [hv]; exact hw)
      have hM : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ lv.M := by
        intro hd
        have hl : (lv.M : ℕ) = Dd.Q.g1 * Dd.Q.g2 := hlev
        rw [hl, ← hpr.1, ← hpr.2.1] at hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
        · exact ng1 ((Nat.prime_dvd_prime_iff_eq hp pg1).1 h)
        · exact ng2 ((Nat.prime_dvd_prime_iff_eq hp pg2).1 h)
      obtain ⟨-, b1, b2⟩ := hnu E H (Dw (ι j)) lv (Xo (ι j)) c hstar (hEx j) (hPk j) N (ι j) pl (Dd.aL (ι j)) (Dd.nW (ι j))
        Dd.Q.T O.b O.L (O.wt j) j1 j2 hPl jp jq jD jG (hN.wt_sum j) (hN.wt_b j) (placeBelow (K := c.F) v)
        (by rw [hr, ← t5]; exact n2) (by rw [hr, ← t3]; exact nq) (by rw [hr, ← t4]; exact nd) (by rw [hr, ← t1]; exact ng1)
        (by rw [hr, ← t2]; exact ng2) (by rw [hr]; exact hM)
      rw [hr] at b1 b2
      constructor
      · have hm' := err_mono_leaf Cc O.C O.k O.m O.f (O.wt j) O.Se (N.Sc + N.eta) (O.th (Formalism.EigenvalueLevelCeiling.plc w))
          (Formalism.EigenvalueLevelCeiling.plc w) O.T O.X2 hCc hCcC hk hm hf (hb.le.trans (hN.wt_b j)) hN.Se_ge (add_nonneg hSc heta)
          (by rw [hN.th_eq]; exact thl_nonneg_leaf _ _) (Nat.cast_nonneg _)
        rw [← hN.th_eq, ← hN.k_eq, ← hN.m_eq, ← hN.f_eq, ← hN.depthNumbers_threshold_eq] at b1
        unfold nuWAt at e1
        unfold OnObj.aE OnObj.A1 OnObj.Akw
        rw [hF, hN.ad_eq]
        linarith
      · intro hY
        apply e2
        apply b2
        have h1 := hN.DF_ge j
        have h0 : (0 : ℝ) ≤ O.DF := le_trans (Nat.cast_nonneg _) h1
        have h2 : O.DF ≤ O.Y := by
          unfold OnObj.Y
          nlinarith
        have : ((DF (Dw (ι j)) (Dd.aL (ι j)) : ℕ) : ℝ) < (Formalism.EigenvalueLevelCeiling.plc w : ℝ) := lt_of_le_of_lt (h1.trans h2) hY
        exact_mod_cast this
    have k1 := key w rfl
    have k2 := key (Formalism.DivisionValues.conjPl w) (Formalism.EigenvalueLevelCeiling.plc_conjPl w)
    refine ⟨fun _ => ⟨k1.1, k2.1⟩, fun hY => ⟨k1.2 hY, k2.2 hY, ?_⟩⟩
    rw [hF]
    obtain ⟨θ0, hdeg⟩ := jG.deg
    exact (GlobalTheory.T.forcedContent_bounds_programmeValue_goodPrime N (ι j) _ hp (t5 ▸ n2) (t3 ▸ nq) (t4 ▸ nd) (t1 ▸ ng1) (t2 ▸ ng2) (fun z => (hdeg.w_pos z).le) jG.ratio).1

end GlobalTheory.GoodDepth
