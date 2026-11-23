import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem tendsto_sum_primesIn {d : IndexData} (S : EndSystem d) (B0 : ℕ) (g : ℕ → ℝ)
    (hg : Summable (fun p : primesAbove S B0 => g p)) :
    Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, g p) atTop
      (𝓝 (∑' p : primesAbove S B0, g p)) := by
  have hs : Summable ((primesAbove S B0).indicator g) := summable_subtype_iff_indicator.mp hg
  rw [_root_.tsum_subtype]
  have h' := (tendsto_add_atTop_iff_nat 1).mpr hs.hasSum.tendsto_sum_nat
  refine h'.congr (fun B => ?_)
  have hsub : primesIn S B0 B ⊆ range (B + 1) := by
    intro p hp
    simp only [primesIn, mem_filter, mem_Ioc] at hp
    exact mem_range.2 (Nat.lt_succ_of_le hp.1.2)
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [primesIn, mem_filter, mem_Ioc] at hp
    exact Set.indicator_of_mem (show p ∈ primesAbove S B0 from ⟨hp.2.1, hp.2.2, hp.1.1⟩) g
  · intro p hp hpn
    refine Set.indicator_of_notMem (fun hmem => hpn ?_) g
    obtain ⟨h1, h2, h3⟩ := hmem
    simp only [primesIn, mem_filter, mem_Ioc]
    exact ⟨⟨h3, Nat.le_of_lt_succ (mem_range.1 hp)⟩, h1, h2⟩

theorem homDecomp_exists {d : IndexData} {F : XPoly d} (hF : F.IsHomogeneous (d.D + 1)) :
    ∃ Q : ℕ → Fin d.f → XPoly d, IsHomDecomp d F Q := by
  obtain ⟨Q, hQh, hQ⟩ :=
    RestTerms.CoinvAboveTop.full ℚ d.f d.N (d.D + 1) F hF (Nat.lt_succ_self _)
  exact ⟨Q, hF, fun k _ τ => hQh k τ, hQ⟩

theorem combo_tendsto (h82 : HeightSumIdentity.Statement) (hsum : RestSummable.Statement)
    {d : IndexData} (S : EndSystem d) (hin : HeightIdentityInputs S) (B0 : ℕ)
    (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d) (hQ : IsHomDecomp d F Q) :
    ∃ L : ℝ, Tendsto (fun B : ℕ => aB S B0 B * (shSum d F : ℝ) + bB S B0 B * (totSum d F : ℝ))
      atTop (𝓝 L) := by
  obtain ⟨B1, hB1⟩ := h82 d S hin B0
  obtain ⟨C, hC⟩ := hB1 F Q hQ
  have hR : Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) atTop
      (𝓝 (restTot S B0 Q)) :=
    tendsto_sum_primesIn S B0 _ (summable_abs_iff.mp (hsum d S B0 F Q hQ.2.2))
  have hlog : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).const_mul C
    rw [mul_zero] at h
    refine h.congr (fun B => ?_)
    simp [mul_div_assoc]
  have hE : Tendsto (fun B : ℕ => S.PP B0 F - (S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
      bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_ge_atTop (max (B0 + 1) B1)] with B hB
    rw [Real.norm_eq_abs]
    exact hC B (lt_of_lt_of_le (Nat.lt_succ_self B0) (le_trans (le_max_left _ _) hB))
      (le_trans (le_max_right _ _) hB)
  refine ⟨(0 - S.PP B0 F + S.vol * S.hh F + restTot S B0 Q) / S.vol, ?_⟩
  have hc1 : Tendsto (fun _ : ℕ => S.PP B0 F) atTop (𝓝 (S.PP B0 F)) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => S.vol * S.hh F) atTop (𝓝 (S.vol * S.hh F)) :=
    tendsto_const_nhds
  refine ((((hE.sub hc1).add hc2).add hR).div_const S.vol).congr (fun B => ?_)
  rw [div_eq_iff S.vol_pos.ne']
  ring

theorem LimitsExist.proof (h82 : HeightSumIdentity.Statement) (hpair : ShTotInvertiblePair.Statement)
    (hsum : RestSummable.Statement) : LimitsExist.Statement := by
  intro d S hin B0
  obtain ⟨F1, F2, hF1, hF2, hdet⟩ := hpair d S.f_pos
  obtain ⟨Q1, hQ1⟩ := homDecomp_exists hF1
  obtain ⟨Q2, hQ2⟩ := homDecomp_exists hF2
  obtain ⟨L1, h1⟩ := combo_tendsto h82 hsum S hin B0 F1 Q1 hQ1
  obtain ⟨L2, h2⟩ := combo_tendsto h82 hsum S hin B0 F2 Q2 hQ2
  have hdetR : (shSum d F1 : ℝ) * (totSum d F2 : ℝ) - (totSum d F1 : ℝ) * (shSum d F2 : ℝ) ≠ 0 := by
    exact_mod_cast hdet
  refine ⟨((totSum d F2 : ℝ) * L1 - (totSum d F1 : ℝ) * L2) /
      ((shSum d F1 : ℝ) * (totSum d F2 : ℝ) - (totSum d F1 : ℝ) * (shSum d F2 : ℝ)),
    ((shSum d F1 : ℝ) * L2 - (shSum d F2 : ℝ) * L1) /
      ((shSum d F1 : ℝ) * (totSum d F2 : ℝ) - (totSum d F1 : ℝ) * (shSum d F2 : ℝ)), ?_, ?_⟩
  · refine (((h1.const_mul (totSum d F2 : ℝ)).sub (h2.const_mul (totSum d F1 : ℝ))).div_const
      _).congr (fun B => ?_)
    rw [div_eq_iff hdetR]
    ring
  · refine (((h2.const_mul (shSum d F1 : ℝ)).sub (h1.const_mul (shSum d F2 : ℝ))).div_const
      _).congr (fun B => ?_)
    rw [div_eq_iff hdetR]
    ring

end GroundTheory.Heights₂.Heights.TheoremB
