import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem

noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Topology Filter Metric Set
open scoped ENNReal

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def tubeS (H : Subgroup G) (V : Set G) (S : Set H) : Set G := {g | ∃ a ∈ V, ∃ h ∈ S, g = a * (h : G)}

theorem mem_tubeS_mul_iff (H : Subgroup G) {V : Set G} (hV : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ H → a = b)
    (S : Set H) {a : G} (ha : a ∈ V) (h0 h : H) :
    a * (h0 : G) * (h : G) ∈ tubeS H V S ↔ h0 * h ∈ S := by
  constructor
  · rintro ⟨a', ha', h', hh', he⟩
    have hmem : a⁻¹ * a' ∈ H := by
      have : a⁻¹ * a' = (h0 : G) * (h : G) * (h' : G)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← he, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact H.mul_mem (H.mul_mem h0.2 h.2) (H.inv_mem h'.2)
    have haa : a = a' := hV a ha a' ha' hmem
    subst haa
    have : h0 * h = h' := by
      apply Subtype.ext
      have := he
      rw [mul_assoc] at this
      simpa using mul_left_cancel this
    rw [this]
    exact hh'
  · intro hS
    exact ⟨a, ha, h0 * h, hS, by simp [mul_assoc]⟩

theorem tube_meas (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) {V : Set G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ H → a = b) {S : Set H} (hS : MeasurableSet S)
    (hT : MeasurableSet (tubeS H V S)) (hVH : MeasurableSet (tubeS H V univ)) :
    ν univ * μ (tubeS H V S) = ν S * μ (tubeS H V univ) := by
  have hf : Measurable ((tubeS H V S).indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hT
  have hmeas2 : AEMeasurable (Function.uncurry fun (g : G) (h : H) =>
      (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G))) (μ.prod ν) :=
    (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable).aemeasurable
  have e1 : ∫⁻ g, ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂ν ∂μ =
      ν univ * μ (tubeS H V S) := by
    rw [lintegral_lintegral_swap hmeas2]
    have : ∀ h : H, ∫⁻ g, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂μ =
        ∫⁻ g, (tubeS H V S).indicator (1 : G → ℝ≥0∞) g ∂μ := fun h =>
      PI.AprimeInfA.lintegral_mul_right_of_mem μ H ν h0 hfin h hf
    simp_rw [this]
    rw [lintegral_const, lintegral_indicator_one hT, mul_comm]
  have e2 : ∀ g, ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂ν =
      (tubeS H V univ).indicator (fun _ => ν S) g := by
    intro g
    by_cases hg : g ∈ tubeS H V univ
    · obtain ⟨a, ha, h0', -, rfl⟩ := hg
      have hm : a * (h0' : G) ∈ tubeS H V univ := ⟨a, ha, h0', mem_univ _, rfl⟩
      rw [indicator_of_mem hm]
      have hpt : ∀ h : H, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (a * (h0' : G) * (h : G)) =
          S.indicator (1 : H → ℝ≥0∞) (h0' * h) := by
        intro h
        by_cases hh : h0' * h ∈ S
        · rw [indicator_of_mem ((mem_tubeS_mul_iff H hV S ha h0' h).2 hh), indicator_of_mem hh]
          simp
        · rw [indicator_of_notMem (fun c => hh ((mem_tubeS_mul_iff H hV S ha h0' h).1 c)),
            indicator_of_notMem hh]
      calc ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (a * (h0' : G) * (h : G)) ∂ν
          = ∫⁻ h, S.indicator (1 : H → ℝ≥0∞) (h0' * h) ∂ν := lintegral_congr hpt
        _ = ∫⁻ h, S.indicator (1 : H → ℝ≥0∞) h ∂ν :=
            lintegral_mul_left_eq_self (fun h => S.indicator (1 : H → ℝ≥0∞) h) h0'
        _ = ν S := lintegral_indicator_one hS
    · rw [indicator_of_notMem hg]
      have hz : ∀ h : H, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) = 0 := by
        intro h
        apply indicator_of_notMem
        rintro ⟨a, ha, h', -, he⟩
        refine hg ⟨a, ha, h' * h⁻¹, mem_univ _, ?_⟩
        have : g = a * (h' : G) * (h : G)⁻¹ := by rw [← he]; group
        rw [this]
        simp [mul_assoc]
      simp [hz]
  calc ν univ * μ (tubeS H V S)
      = ∫⁻ g, ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂ν ∂μ := e1.symm
    _ = ∫⁻ g, (tubeS H V univ).indicator (fun _ => ν S) g ∂μ := lintegral_congr e2
    _ = ν S * μ (tubeS H V univ) := lintegral_indicator_const hVH _

end Abstract

section Ratio

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

structure TubeChart (μ : Measure G) (H : Subgroup G) (ν : Measure H) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → G) (χ : EuclideanSpace ℝ η → H) (r0 : ℝ)
    (d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ) (e : EuclideanSpace ℝ η → ℝ) : Prop where
  pos : 0 < r0
  inj : ∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0, (κ a)⁻¹ * κ b ∈ H → a = b
  mS : ∀ s, 0 < s → s ≤ r0 → MeasurableSet (χ '' ball 0 s)
  mT : ∀ ρ s, 0 < ρ → ρ ≤ r0 → 0 < s → s ≤ r0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s))
  mH : ∀ ρ, 0 < ρ → ρ ≤ r0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) univ)
  densG : ∀ ρ s, 0 < ρ → ρ ≤ r0 → 0 < s → s ≤ r0 →
    μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) = ∫⁻ p in ball 0 ρ ×ˢ ball 0 s, ENNReal.ofReal (d p)
  densH : ∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)

theorem tube_bounds (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ∞) {ι η : Type} [Fintype ι] [Fintype η]
    {κ : EuclideanSpace ℝ ι → G} {χ : EuclideanSpace ℝ η → H} {r0 : ℝ} {d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ}
    {e : EuclideanSpace ℝ η → ℝ} (hC : TubeChart μ H ν κ χ r0 d e)
    {ε s ρ : ℝ} (hε : 0 < ε) (hεd : ε < d 0) (hεe : ε < e 0) (hs : 0 < s) (hsr : s ≤ r0) (hρ : 0 < ρ)
    (hρs : ρ ≤ s) (hdε : ∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ‖p‖ < s → |d p - d 0| < ε)
    (heε : ∀ y : EuclideanSpace ℝ η, ‖y‖ < s → |e y - e 0| < ε) :
    0 < μ (tubeS H (κ '' ball 0 ρ) univ) ∧ μ (tubeS H (κ '' ball 0 ρ) univ) < ⊤ ∧
    (d 0 - ε) / (e 0 + ε) * (ν univ).toReal ≤
      (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal ∧
    (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal ≤
      (d 0 + ε) / (e 0 - ε) * (ν univ).toReal := by
  have hρr : ρ ≤ r0 := hρs.trans hsr
  set A := ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s with hA
  have hAm : MeasurableSet A := measurableSet_ball.prod measurableSet_ball
  have hAn : ∀ p ∈ A, ‖p‖ < s := by
    intro p hp
    rw [Prod.norm_def]
    have h1 : ‖p.1‖ < ρ := mem_ball_zero_iff.1 hp.1
    have h2 : ‖p.2‖ < s := mem_ball_zero_iff.1 hp.2
    exact max_lt (h1.trans_le hρs) h2
  set Lρ := volume (ball (0 : EuclideanSpace ℝ ι) ρ) with hLρ
  set Ls := volume (ball (0 : EuclideanSpace ℝ η) s) with hLs
  have hLρ0 : 0 < Lρ := measure_ball_pos _ _ hρ
  have hLs0 : 0 < Ls := measure_ball_pos _ _ hs
  have hLρt : Lρ < ⊤ := measure_ball_lt_top
  have hLst : Ls < ⊤ := measure_ball_lt_top
  have hvA : volume A = Lρ * Ls := by rw [hA, Measure.volume_eq_prod, Measure.prod_prod]

  have hVS_hi : μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) ≤ ENNReal.ofReal (d 0 + ε) * (Lρ * Ls) := by
    rw [hC.densG ρ s hρ hρr hs hsr, ← hvA, ← setLIntegral_const]
    refine setLIntegral_mono' hAm fun p hp => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (hdε p (hAn p hp)); linarith
  have hVS_lo : ENNReal.ofReal (d 0 - ε) * (Lρ * Ls) ≤ μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) := by
    rw [hC.densG ρ s hρ hρr hs hsr, ← hvA, ← setLIntegral_const]
    refine setLIntegral_mono' hAm fun p hp => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (hdε p (hAn p hp)); linarith
  have hS_hi : ν (χ '' ball 0 s) ≤ ENNReal.ofReal (e 0 + ε) * Ls := by
    rw [hC.densH s hs hsr, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (heε y (mem_ball_zero_iff.1 hy)); linarith
  have hS_lo : ENNReal.ofReal (e 0 - ε) * Ls ≤ ν (χ '' ball 0 s) := by
    rw [hC.densH s hs hsr, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (heε y (mem_ball_zero_iff.1 hy)); linarith

  have hV : ∀ a ∈ κ '' ball (0 : EuclideanSpace ℝ ι) ρ, ∀ b ∈ κ '' ball (0 : EuclideanSpace ℝ ι) ρ,
      a⁻¹ * b ∈ H → a = b := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hm
    rw [hC.inj x (ball_subset_ball hρr hx) y (ball_subset_ball hρr hy) hm]
  have hid := tube_meas μ H ν hν0 hνf hV (hC.mS s hs hsr) (hC.mT ρ s hρ hρr hs hsr) (hC.mH ρ hρ hρr)
  set N := ν univ with hN
  set a := μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) with ha
  set b := μ (tubeS H (κ '' ball 0 ρ) univ) with hb
  set c := ν (χ '' ball 0 s) with hc
  have hde : 0 < d 0 - ε := by linarith
  have hee : 0 < e 0 - ε := by linarith
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hLρt.ne hLst.ne)) hVS_hi
  have ha0 : a ≠ 0 := by
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ hVS_lo
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hde).ne' (ENNReal.mul_pos hLρ0.ne' hLs0.ne').ne'
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLst.ne) hS_hi
  have hc0 : c ≠ 0 := by
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ hS_lo
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hee).ne' hLs0.ne'
  have hbt : b ≠ ⊤ := by
    intro hb'
    have : N * a = ⊤ := by rw [hid, hb', ENNReal.mul_top hc0]
    exact ENNReal.mul_ne_top hνf hat this
  have hb0 : b ≠ 0 := by
    intro hb'
    have : N * a = 0 := by rw [hid, hb', mul_zero]
    rcases mul_eq_zero.1 this with h | h
    · exact hν0 h
    · exact ha0 h
  refine ⟨pos_iff_ne_zero.2 hb0, lt_top_iff_ne_top.2 hbt, ?_, ?_⟩
  all_goals
    have hidR : N.toReal * a.toReal = c.toReal * b.toReal := by
      rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hid]
    have hlρ : 0 < Lρ.toReal := ENNReal.toReal_pos hLρ0.ne' hLρt.ne
    have hls : 0 < Ls.toReal := ENNReal.toReal_pos hLs0.ne' hLst.ne
    have hNr : 0 < N.toReal := ENNReal.toReal_pos hν0 hνf
    have hbr : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
    have ahi : a.toReal ≤ (d 0 + ε) * (Lρ.toReal * Ls.toReal) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hLρt.ne hLst.ne)) hVS_hi
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have alo : (d 0 - ε) * (Lρ.toReal * Ls.toReal) ≤ a.toReal := by
      have := ENNReal.toReal_mono hat hVS_lo
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hde.le] at this
    have chi : c.toReal ≤ (e 0 + ε) * Ls.toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLst.ne) hS_hi
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have clo : (e 0 - ε) * Ls.toReal ≤ c.toReal := by
      have := ENNReal.toReal_mono hct hS_lo
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hee.le] at this
  ·
    rw [le_div_iff₀ hlρ, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have h1 : N.toReal * ((d 0 - ε) * (Lρ.toReal * Ls.toReal)) ≤ b.toReal * ((e 0 + ε) * Ls.toReal) :=
      calc N.toReal * ((d 0 - ε) * (Lρ.toReal * Ls.toReal)) ≤ N.toReal * a.toReal :=
            mul_le_mul_of_nonneg_left alo hNr.le
        _ = c.toReal * b.toReal := hidR
        _ ≤ ((e 0 + ε) * Ls.toReal) * b.toReal := mul_le_mul_of_nonneg_right chi hbr.le
        _ = b.toReal * ((e 0 + ε) * Ls.toReal) := mul_comm _ _
    have h2 : ((d 0 - ε) * N.toReal * Lρ.toReal) * Ls.toReal ≤ (b.toReal * (e 0 + ε)) * Ls.toReal := by
      nlinarith
    exact le_of_mul_le_mul_right h2 hls
  ·
    rw [div_le_iff₀ hlρ, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hee]
    have h1 : b.toReal * ((e 0 - ε) * Ls.toReal) ≤ N.toReal * ((d 0 + ε) * (Lρ.toReal * Ls.toReal)) :=
      calc b.toReal * ((e 0 - ε) * Ls.toReal) = ((e 0 - ε) * Ls.toReal) * b.toReal := mul_comm _ _
        _ ≤ c.toReal * b.toReal := mul_le_mul_of_nonneg_right clo hbr.le
        _ = N.toReal * a.toReal := hidR.symm
        _ ≤ N.toReal * ((d 0 + ε) * (Lρ.toReal * Ls.toReal)) := mul_le_mul_of_nonneg_left ahi hNr.le
    have h2 : (b.toReal * (e 0 - ε)) * Ls.toReal ≤ ((d 0 + ε) * N.toReal * Lρ.toReal) * Ls.toReal := by
      nlinarith
    exact le_of_mul_le_mul_right h2 hls

theorem tube_ratio (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ∞) {ι η : Type} [Fintype ι] [Fintype η]
    {κ : EuclideanSpace ℝ ι → G} {χ : EuclideanSpace ℝ η → H} {r0 : ℝ} {d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ}
    {e : EuclideanSpace ℝ η → ℝ} (hC : TubeChart μ H ν κ χ r0 d e) (hd : ContinuousAt d 0) (hd0 : 0 < d 0)
    (he : ContinuousAt e 0) (he0 : 0 < e 0) :
    (∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) univ) ∧
      0 < μ (tubeS H (κ '' ball 0 ρ) univ) ∧ μ (tubeS H (κ '' ball 0 ρ) univ) < ⊤) ∧
    Tendsto (fun ρ => (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (d 0 / e 0 * (ν univ).toReal)) := by

  have hrad : ∀ ε > 0, ∃ s, 0 < s ∧ s ≤ r0 ∧
      (∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ‖p‖ < s → |d p - d 0| < ε) ∧
      (∀ y : EuclideanSpace ℝ η, ‖y‖ < s → |e y - e 0| < ε) := by
    intro ε hε
    obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hd ε hε
    obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1 he ε hε
    refine ⟨min (min δ1 δ2) r0, lt_min (lt_min hδ1 hδ2) hC.pos, min_le_right _ _, ?_, ?_⟩
    · intro p hp
      have := h1 (x := p) (by rw [dist_zero_right]; exact hp.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      rwa [Real.dist_eq] at this
    · intro y hy
      have := h2 (x := y) (by rw [dist_zero_right]; exact hy.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      rwa [Real.dist_eq] at this
  constructor
  · have hε : 0 < min (d 0) (e 0) / 2 := by positivity
    obtain ⟨s, hs, hsr, hdε, heε⟩ := hrad _ hε
    refine ⟨s, hs, fun ρ hρ hρs => ?_⟩
    have hm := min_le_left (d 0) (e 0)
    have hm' := min_le_right (d 0) (e 0)
    obtain ⟨h1, h2, -, -⟩ := tube_bounds μ H ν hν0 hνf hC hε (by linarith) (by linarith) hs hsr hρ hρs.le hdε heε
    exact ⟨hC.mH ρ hρ (hρs.le.trans hsr), h1, h2⟩
  · set T := d 0 / e 0 * (ν univ).toReal with hT
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    have hU : Tendsto (fun ε : ℝ => (d 0 + ε) / (e 0 - ε) * (ν univ).toReal) (𝓝 0) (𝓝 T) := by
      have : ContinuousAt (fun ε : ℝ => (d 0 + ε) / (e 0 - ε) * (ν univ).toReal) 0 :=
        ((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
          (by simp; exact he0.ne')).mul continuousAt_const
      simpa [hT] using this.tendsto
    have hL : Tendsto (fun ε : ℝ => (d 0 - ε) / (e 0 + ε) * (ν univ).toReal) (𝓝 0) (𝓝 T) := by
      have : ContinuousAt (fun ε : ℝ => (d 0 - ε) / (e 0 + ε) * (ν univ).toReal) 0 :=
        ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
          (by simp; exact he0.ne')).mul continuousAt_const
      simpa [hT] using this.tendsto
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < d 0 ∧ ε < e 0 ∧
        (d 0 + ε) / (e 0 - ε) * (ν univ).toReal < T + δ ∧ T - δ < (d 0 - ε) / (e 0 + ε) * (ν univ).toReal := by
      refine Filter.Eventually.and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)) (nhdsWithin_le_nhds ?_)
      refine (gt_mem_nhds hd0).and ((gt_mem_nhds he0).and
        ((hU.eventually (gt_mem_nhds (by linarith : T < T + δ))).and
          (hL.eventually (lt_mem_nhds (by linarith : T - δ < T)))))
    obtain ⟨ε, hε, hεd, hεe, hεU, hεL⟩ := ev.exists
    obtain ⟨s, hs, hsr, hdε, heε⟩ := hrad ε hε
    refine ⟨s, hs, fun {ρ} hρ hρd => ?_⟩
    have hρ' : 0 < ρ := hρ
    have hρs : ρ ≤ s := by rw [Real.dist_eq, sub_zero, abs_of_pos hρ'] at hρd; exact hρd.le
    obtain ⟨-, -, hlo, hhi⟩ := tube_bounds μ H ν hν0 hνf hC hε hεd hεe hs hsr hρ' hρs hdε heε
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith

end Ratio

end PI.AprimeInfG
