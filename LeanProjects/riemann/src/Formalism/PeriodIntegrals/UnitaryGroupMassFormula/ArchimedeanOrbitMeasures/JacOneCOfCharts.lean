import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfFibres
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def JacOneCFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem jacOneCFor_of {Pr : ChartPred} (hK : KPos) (hR : LocRatioFor Pr) : JacOneCFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨V, W, hVW, hsh, hlim⟩ := hR X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  set L : ℕ → ENNReal := fun n => μinf (BoxT X u' a (V n) (W n)) with hL
  set B : ℕ → ENNReal := fun n => νinf (W n) with hB
  set M : ℕ → ENNReal := fun n => X.measG.μGinf (TubeG X u' (V n)) with hM
  set A : ℕ → ENNReal := fun n => ∫⁻ T in W n, c T ∂νinf with hA

  have key : ∀ n, L n = A n * M n := by
    intro n
    obtain ⟨hWm, hWs, -, -, hU, hBm, hBI, -, hTm, -, hMt⟩ := hVW n
    have h := hid ((BoxT X u' a (V n) (W n)).indicator 1) (measurable_one.indicator hBm) (W n)
      hWs hWm
    have hsub : BoxT X u' a (V n) (W n) ⊆
        gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' (W n)) ∩ IndI X := by
      intro y hy
      refine ⟨?_, hBI hy⟩
      obtain ⟨T, hTW, g, -, rfl⟩ := hy
      refine ⟨T, hTW, ?_⟩
      rw [gramR_smul, hC.2.2.2 T (hΩ₂ (hWs hTW))]
    rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm, Set.inter_eq_left.2 hsub] at h
    have hin : ∀ T ∈ W n, ∫⁻ g, (BoxT X u' a (V n) (W n)).indicator 1 (g • rmulT X (a T) (Y0 X u'))
        ∂X.measG.μGinf = M n := by
      intro T hTW
      have hs := pre_box X u' hT hC (V n) (hWs.trans hΩ₂) hU T hTW
      have e : (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
          (BoxT X u' a (V n) (W n)).indicator (1 : TupI X → ENNReal) (g • rmulT X (a T) (Y0 X u'))) =
          (TubeG X u' (V n)).indicator 1 := by
        funext g
        by_cases hg : g ∈ TubeG X u' (V n)
        · have h4 : g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_mem hg, Set.indicator_of_mem h4]; rfl
        · have h4 : g • rmulT X (a T) (Y0 X u') ∉ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h4]
      rw [e, lintegral_indicator_one hTm]
    rw [setLIntegral_congr_fun hWm (fun T hT' => by rw [hin T hT'])] at h
    rw [lintegral_mul_const' _ _ hMt.ne] at h
    exact h
  have hAt : ∀ n, A n ≠ ⊤ := by
    intro n hA'
    obtain ⟨-, -, -, -, -, -, -, hLt, -, hM0, -⟩ := hVW n
    have : L n = ⊤ := by rw [key n, hA', ENNReal.top_mul hM0.ne']
    exact absurd this hLt.ne
  have e1 : ∀ n, (L n).toReal / ((B n).toReal * (M n).toReal) = (A n).toReal / (B n).toReal := by
    intro n
    obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt⟩ := hVW n
    have hMr : 0 < (M n).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
    rw [key n, ENNReal.toReal_mul]
    field_simp
  have hlim' : Tendsto (fun n => (L n).toReal / ((B n).toReal * (M n).toReal)) atTop (𝓝 (KVal X u')⁻¹) := hlim

  have hge : ∀ b : ENNReal, b < c (TI X u' hT) → b.toReal ≤ (KVal X u')⁻¹ := by
    intro b hb
    have hU : c ⁻¹' Set.Ioi b ∈ 𝓝 (TI X u' hT) := hcc (Ioi_mem_nhds hb)
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hlow : b * B n ≤ A n :=
      calc b * B n = ∫⁻ _ in W n, b ∂νinf := (setLIntegral_const _ _).symm
        _ ≤ A n := lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
            (hn hT').le))
    rw [e1 n, le_div_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hAt n) hlow

  have hle : ∀ b : ENNReal, c (TI X u' hT) < b → b ≠ ⊤ → (KVal X u')⁻¹ ≤ b.toReal := by
    intro b hb hbt
    have hU : c ⁻¹' Set.Iio b ∈ 𝓝 (TI X u' hT) := hcc (Iio_mem_nhds hb)
    refine le_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hup : A n ≤ b * B n :=
      calc A n ≤ ∫⁻ _ in W n, b ∂νinf := lintegral_mono_ae ((ae_restrict_iff' hWm).2
            (Eventually.of_forall fun T hT' => (hn hT').le))
        _ = b * B n := setLIntegral_const _ _
    rw [e1 n, div_le_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hbt hBt.ne) hup

  have hfin : c (TI X u' hT) ≠ ⊤ := by
    intro htop
    have h1 := hge (ENNReal.ofReal ((KVal X u')⁻¹ + 1)) (by rw [htop]; exact ENNReal.ofReal_lt_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  set c₀ : ℝ := (c (TI X u' hT)).toReal with hc₀
  have hle' : c₀ ≤ (KVal X u')⁻¹ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hcε : c₀ - ε ≤ 0
    · have : 0 < (KVal X u')⁻¹ := inv_pos.2 hK0
      linarith
    · push_neg at hcε
      have hb : ENNReal.ofReal (c₀ - ε) < c (TI X u' hT) := by
        rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have := hge _ hb
      rw [ENNReal.toReal_ofReal hcε.le] at this
      linarith
  have hge' : (KVal X u')⁻¹ ≤ c₀ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
    have hb : c (TI X u' hT) < ENNReal.ofReal (c₀ + ε) := by
      rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := hle _ hb ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hceq : c₀ = (KVal X u')⁻¹ := le_antisymm hle' hge'
  rw [← ENNReal.ofReal_toReal hfin, ← hc₀, hceq, ENNReal.ofReal_inv_of_pos hK0]

theorem jacOneC_of_charts (hK : KPos) (hU : UnimodInf) (hW : WittNear) (hG : GoodChartEx) : JacOneC := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨Ω', a₂, hC₂, hgood⟩ := hG X u' ψ hT μinf νinf fibInf hP
  have hev : ∀ᶠ T in 𝓝 (TI X u' hT), ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u') := by
    obtain ⟨ι, _, κ, -, η, _, eT, eH, cμ, cν, Ψ', U, -, -, -, -, -, -, -, -, hev0, -⟩ := hgood
    filter_upwards [hev0, hC.1, hC₂.1] with T h1 h2 h3
    exact hW X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T ⟨h2, h3⟩ h1.1
  set Ω₃ := Ω₂ ∩ Ω' ∩ {T | ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')} with hΩ₃
  have hΩ₃n : Ω₃ ∈ 𝓝 (TI X u' hT) := inter_mem (inter_mem hΩ₂n hC₂.1) hev
  have hid₂ : PolId X u' μinf νinf a₂ Ω₃ c := by
    intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans (Set.inter_subset_left.trans Set.inter_subset_left)) hSm]
    refine setLIntegral_congr_fun hSm (fun T hT' => ?_)
    obtain ⟨h, eh⟩ := (hS hT').2
    rw [eh]
    congr 1
    have e : ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
        φ (g • h • rmulT X (a₂ T) (Y0 X u')) = (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) (g * h) := by
      intro g; simp only [mul_smul]
    simp_rw [e]
    exact hU X u' ψ hT μinf νinf fibInf hP (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) h
  exact jacOneCFor_of hK (locRatioFor_of hK splitAsym_good) X u' ψ hT μinf νinf fibInf hP Ω' a₂ hC₂ hgood Ω₃
    (Set.inter_subset_left.trans Set.inter_subset_right) hΩ₃n c hcc hid₂

end PI.AprimeInfW
