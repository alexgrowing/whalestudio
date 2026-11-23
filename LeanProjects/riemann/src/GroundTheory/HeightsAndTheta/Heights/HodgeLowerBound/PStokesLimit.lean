import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitPos.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hTel : StokesTelescope.Statement) (hNs : NbarSemipos.Statement) (hTp : StokesLimitTp.Statement)
    (hT : StokesLimitT.Statement) (hE : StokesLimitEps.Statement) : StokesLimitPos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B a hII hpos hB hAr hyp
  have hc0 : (0 : ℝ) ≤ ((D.n + 1 : ℕ) : ℝ) := by positivity

  have step : ∀ m : ℕ, ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1) ≤ X.topNLim B 1 (m + 1) := by
    intro m
    have hp : 1 ≤ 1 := le_rfl
    have hpq : 1 ≤ m + 1 := by omega
    obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq
    obtain ⟨tP, htP, hP⟩ := hpos B 1 (m + 1) hB hp hpq
    obtain ⟨tH, htH, hH⟩ := hyp 1 (m + 1) hp hpq
    obtain ⟨t₂, ht₂, hTp'⟩ := hTp II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq

    have stepT : ∀ t : ℝ, 0 < t → t ≤ min t₁ t₂ →
        ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
          ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t ≤ X.topN B 1 (m + 1) t := by
      intro t ht0 ht1
      have hNt := hN t ht0 (ht1.trans (min_le_left _ _))
      obtain ⟨hlim, hVb⟩ := hTp' t ht0 (ht1.trans (min_le_right _ _)) hNt
      have hev : ∀ᶠ t' in 𝓝[>] (0 : ℝ),
          ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
            ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t' ≤ X.topN B 1 (m + 1) t := by
        filter_upwards [Ioc_mem_nhdsGT (lt_min htP htH)] with t' ht'
        have hsP := (hP t' ht'.1 (ht'.2.trans (min_le_left _ _))).1
        have htel := hTel II Ψ K ι Ω E D O Lt X B 1 (m + 1) t t' hII hpq hsP hNt
        have hh := hH t' ht'.1 (ht'.2.trans (min_le_right _ _))
        have hdeg : geomDegMUc X.H X.S' B 1 (m + 1) t' = X.degN B 1 (m + 1) t := by
          unfold geomDegMUc ComponentSetting.degN
          congr 1
          rw [hG K ι Ω D.y D.n _ D.arith hsP.1, hG K ι Ω D.y D.n _ D.arith hNt.1]
          congr 1
          simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
          rfl
        rw [hdeg] at hh
        have e : ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) = ((D.n + 1 : ℕ) : ℝ) * (a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t := by ring
        linarith
      have hL : Tendsto (fun t' => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t') (𝓝[>] 0)
          (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vlim B 1 (m + 1) t)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
      have h1 := le_of_tendsto hL hev
      have h2 := mul_le_mul_of_nonneg_left hVb hc0
      linarith
    obtain ⟨hT1, hT2, hT3⟩ := hT II Ψ K ι Ω E D O Lt X B 1 (m + 1) hII hAr hp hpq
    have hL : Tendsto (fun t => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
        X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t) (𝓝[>] 0)
        (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1))) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hT3)).sub (tendsto_const_nhds.mul hT2)
    refine le_of_tendsto_of_tendsto hL hT1 ?_
    filter_upwards [Ioc_mem_nhdsGT (lt_min ht₁ ht₂)] with t ht using stepT t ht.1 ht.2

  obtain ⟨hE1, hE2, hE3⟩ := hE II Ψ K ι Ω E D O Lt X B hII hAr
  have hε : Tendsto (fun m : ℕ => ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Nat.cast_add, Nat.cast_one] using h0
  have hL : Tendsto (fun m : ℕ => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1)) atTop
      (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2))) :=
    (tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hε.mul tendsto_const_nhds)).mul hE3)).sub
      (tendsto_const_nhds.mul hE2)
  have key := le_of_tendsto_of_tendsto' hL hE1 step
  calc ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H
      = ((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2) := by ring
    _ ≤ arLim X.H X.S B := key

end GroundTheory.Heights₂.Heights.LowerBoundFree
