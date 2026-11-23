import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegCutTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutTailMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

theorem SliceRegTailMass.proof (hMono : SliceRegMassMono.Statement) (hCont : SliceRegMassContinuous.Statement)
    (hLim : SliceRegMassLimit.Statement) (hSec : SliceSectionTailMass.Statement)
    (hReg : SliceRegCutTail.Statement) (hM : SliceCutTailMass.Statement) : SliceRegTailMass.Statement := by
  intro n e h W F u' ℓ hW hF hu hℓ hℓP δ hδ
  set Φ : ℕ → ℝ → ℝ := fun k ε =>
    varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
        (fun _ x => Real.log (h.dualNorm x)) with hΦ
  set L : ℕ → ℝ := fun k => ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
    varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - sliceCut h k x)
      (fun _ x => Real.log (h.dualNorm x)) with hL
  set G : ℕ → ℝ → ℝ := fun k t => if 0 < t then Φ k t else L k with hG
  have hmeas : ∀ k, Measurable fun x => 1 - sliceCut h k x :=
    fun k => measurable_const.sub (SliceCut.measurable h k)
  have hlim : ∀ k, Tendsto (Φ k) (𝓝[>] 0) (𝓝 (L k)) := fun k =>
    hLim n e h W F u' ℓ (sliceCut h k) hW hF hu hℓ hℓP (SliceCut.contDiff h k) (SliceCut.hasCompactSupport h k)
  have hanti : ∀ ε, 0 < ε → Antitone fun k => Φ k ε := fun ε hε k m hkm =>
    hMono n e h W F u' ℓ ε _ _ hW hF hℓ hε (hmeas m) (hmeas k)
      (fun x => by linarith [(SliceCut.mem_Icc h m x).2])
      (fun x => by linarith [SliceCut.monotone h x hkm]) (fun x => by linarith [(SliceCut.mem_Icc h k x).1])
  have hantiL : Antitone L := fun k m hkm =>
    le_of_tendsto_of_tendsto (hlim m) (hlim k) (eventually_nhdsWithin_of_forall fun ε hε => hanti ε hε hkm)
  have hGpos : ∀ k t, 0 < t → G k t = Φ k t := fun k t ht => by simp only [hG, if_pos ht]
  have hG0 : ∀ k, G k 0 = L k := fun k => by simp only [hG, lt_irrefl, if_false]
  have hGcont : ∀ k, ContinuousOn (G k) (Set.Icc 0 1) := by
    intro k t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · subst h0
      refine ContinuousWithinAt.mono ?_ fun x hx => (Set.mem_Ici.mpr hx.1)
      rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hG0]
      exact (hlim k).congr' (eventually_nhdsWithin_of_forall fun ε hε => (hGpos k ε hε).symm)
    · have h1 := hCont n e h W F u' ℓ (fun x => 1 - sliceCut h k x) 1 hW hF hℓ (hmeas k) fun x => by
        rw [abs_le]; constructor <;> linarith [(SliceCut.mem_Icc h k x).1, (SliceCut.mem_Icc h k x).2]
      have h2 : ContinuousOn (Φ k) (Set.Ioi 0) := h1.add continuousOn_const
      have hc := h2.continuousAt (Ioi_mem_nhds hpos)
      exact (hc.congr (eventually_of_mem (Ioi_mem_nhds hpos) fun ε hε => (hGpos k ε hε).symm)).continuousWithinAt
  have hU := Antitone.tendstoUniformlyOn_of_forall_tendsto (f := fun _ => (0 : ℝ)) isCompact_Icc hGcont
    (fun t _ => by
      rcases lt_or_ge 0 t with hpos | hpos
      · simpa only [hGpos _ t hpos] using hanti t hpos
      · simpa only [hG, not_lt.mpr hpos, if_false] using hantiL)
    continuousOn_const
    (fun t ht => by
      rcases ht.1.eq_or_lt with h0 | hpos
      · subst h0
        simp only [hG0]
        have := tendsto_finsetSum (divCycle W u').support fun P hP =>
          (hSec n e h W F u' ℓ hW hF hu hℓ hℓP P hP).const_mul (((divCycle W u' P : ℕ) : ℝ))
        simpa only [mul_zero, Finset.sum_const_zero] using this
      · simp only [hGpos _ t hpos]
        simpa only [add_zero] using (hReg n e h W F u' ℓ t hW hF hℓ hpos).add (hM n e h W F ℓ hW hF hℓ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hU δ hδ)
  refine ⟨K, fun k hk ε hε => ?_⟩
  have := hK k hk ε ⟨hε.1.le, hε.2⟩
  rw [hGpos k ε hε.1, Real.dist_eq, zero_sub, abs_neg] at this
  exact (le_abs_self _).trans this.le

end GroundTheory.Heights₂.Heights
