import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem rmulT_rmulT {D : D7} (X : HidaSetting D) (a b : MfI X) (Y : TupI X) :
    rmulT X b (rmulT X a Y) = rmulT X (a * b) Y := by
  funext d i
  simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem smul_rmulT {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (a : MfI X)
    (Y : TupI X) : g • rmulT X a Y = rmulT X a (g • Y) := by
  funext b i
  change Matrix.mulVec (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).1 (rmulT X a Y b) i =
    ∑ c, a c b * Matrix.mulVec (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).1 (Y c) i
  simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def BoxT {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X)
    (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : Set (HmI X)) : Set (TupI X) :=
  {y | ∃ T ∈ W, ∃ g ∈ V, y = g • rmulT X (a T) (Y0 X u')}

def TubeG {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
    Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  {g | ∃ g' ∈ V, g • Y0 X u' = g' • Y0 X u'}

def ChartPred : Type 1 := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word),
    (∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) →
    Measure (TupI X) → Measure (HmI X) → (HmI X → MfI X) → Prop

def JacOneFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ J : HmI X → ℝ, J (TI X u' hT) = 1 → ContinuousAt J (TI X u' hT) →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c₀ : ENNReal,
      PolId X u' μinf νinf a Ω₂ (fun T => c₀ * ENNReal.ofReal (J T)) → c₀ = (ENNReal.ofReal (KVal X u'))⁻¹

def LocRatioFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal /
        ((νinf (W n)).toReal * (X.measG.μGinf (TubeG X u' (V n))).toReal)) atTop (𝓝 (KVal X u')⁻¹)

def LocRatio : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal /
        ((νinf (W n)).toReal * (X.measG.μGinf (TubeG X u' (V n))).toReal)) atTop (𝓝 (KVal X u')⁻¹)

theorem pre_box {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    {Ω : Set (HmI X)} {a : HmI X → MfI X} (hC : IsChart X u' hT Ω a)
    (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) {W : Set (HmI X)} (hW : W ⊆ Ω)
    (hU : ∀ T ∈ W, IsUnit (a T)) (T : HmI X) (hTW : T ∈ W) :
    {g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J | g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a V W} =
      TubeG X u' V := by
  ext g
  constructor
  · rintro ⟨T₁, hT₁, g', hg', e⟩
    have hG : T = T₁ := by
      apply Subtype.ext
      have h2 := congrArg (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) e
      rw [gramR_smul, gramR_smul, hC.2.2.2 T (hW hTW), hC.2.2.2 T₁ (hW hT₁)] at h2
      exact h2
    subst hG
    refine ⟨g', hg', ?_⟩
    obtain ⟨w, hw⟩ := hU T hTW
    rw [smul_rmulT, smul_rmulT] at e
    have h3 := congrArg (rmulT X (↑w⁻¹ : MfI X)) e
    rwa [rmulT_rmulT, rmulT_rmulT, ← hw, Units.mul_inv, rmulT_one, rmulT_one] at h3
  · rintro ⟨g', hg', e⟩
    refine ⟨T, hTW, g', hg', ?_⟩
    rw [smul_rmulT, smul_rmulT, e]

theorem jacOneFor_of {Pr : ChartPred} (hK : KPos) (hR : LocRatioFor Pr) : JacOneFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr J hJ1 hJc Ω₂ hΩ₂ hΩ₂n c₀ hid
  obtain ⟨V, W, hVW, hsh, hlim⟩ := hR X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  set L : ℕ → ENNReal := fun n => μinf (BoxT X u' a (V n) (W n)) with hL
  set B : ℕ → ENNReal := fun n => νinf (W n) with hB
  set M : ℕ → ENNReal := fun n => X.measG.μGinf (TubeG X u' (V n)) with hM
  set A : ℕ → ENNReal := fun n => ∫⁻ T in W n, c₀ * ENNReal.ofReal (J T) ∂νinf with hA

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

  have bounds : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop,
      c₀ * ENNReal.ofReal (1 - ε) * B n ≤ A n ∧ A n ≤ c₀ * ENNReal.ofReal (1 + ε) * B n := by
    intro ε hε0 hε1
    have hU : J ⁻¹' Set.Ioo (1 - ε) (1 + ε) ∈ 𝓝 (TI X u' hT) :=
      hJc (Ioo_mem_nhds (by rw [hJ1]; linarith) (by rw [hJ1]; linarith))
    filter_upwards [hsh _ hU] with n hn
    have hWm := (hVW n).1
    constructor
    · calc c₀ * ENNReal.ofReal (1 - ε) * B n = ∫⁻ _ in W n, c₀ * ENNReal.ofReal (1 - ε) ∂νinf :=
            (setLIntegral_const _ _).symm
        _ ≤ A n := lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
            by gcongr; exact (hn hT').1.le))
    · calc A n ≤ ∫⁻ _ in W n, c₀ * ENNReal.ofReal (1 + ε) ∂νinf :=
            lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
              by gcongr; exact (hn hT').2.le))
        _ = c₀ * ENNReal.ofReal (1 + ε) * B n := setLIntegral_const _ _

  have hc₀ : c₀ ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn1, -⟩ := (bounds (1 / 2) (by norm_num) (by norm_num)).exists
    obtain ⟨-, -, hB0, -, -, -, -, hLt, -, hM0, -⟩ := hVW n
    have hAt : A n = ⊤ := by
      refine top_le_iff.1 (le_trans (le_of_eq ?_) hn1)
      rw [htop, ENNReal.top_mul (ENNReal.ofReal_pos.2 (by norm_num)).ne', ENNReal.top_mul hB0.ne']
    have : L n = ⊤ := by rw [key n, hAt, ENNReal.top_mul hM0.ne']
    exact absurd this hLt.ne
  set c : ℝ := c₀.toReal with hc

  have pinch : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop,
      c * (1 - ε) ≤ (L n).toReal / ((B n).toReal * (M n).toReal) ∧
        (L n).toReal / ((B n).toReal * (M n).toReal) ≤ c * (1 + ε) := by
    intro ε hε0 hε1
    filter_upwards [bounds ε hε0 hε1] with n hn
    obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hMr : 0 < (M n).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
    have hup : c₀ * ENNReal.ofReal (1 + ε) * B n ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hc₀ ENNReal.ofReal_ne_top) hBt.ne
    have hAt : A n ≠ ⊤ := ne_top_of_le_ne_top hup hn.2
    have e1 : (L n).toReal / ((B n).toReal * (M n).toReal) = (A n).toReal / (B n).toReal := by
      rw [key n, ENNReal.toReal_mul]
      field_simp
    have e2 : (c₀ * ENNReal.ofReal (1 - ε) * B n).toReal = c * (1 - ε) * (B n).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
    have e3 : (c₀ * ENNReal.ofReal (1 + ε) * B n).toReal = c * (1 + ε) * (B n).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
    rw [e1]
    constructor
    · rw [le_div_iff₀ hBr, ← e2]
      exact ENNReal.toReal_mono hAt hn.1
    · rw [div_le_iff₀ hBr, ← e3]
      exact ENNReal.toReal_mono hup hn.2
  have hlim' : Tendsto (fun n => (L n).toReal / ((B n).toReal * (M n).toReal)) atTop (𝓝 (KVal X u')⁻¹) := hlim
  have lo : ∀ ε : ℝ, 0 < ε → ε < 1 → c * (1 - ε) ≤ (KVal X u')⁻¹ := fun ε h0 h1 =>
    ge_of_tendsto hlim' ((pinch ε h0 h1).mono fun _ h => h.1)
  have hi : ∀ ε : ℝ, 0 < ε → ε < 1 → (KVal X u')⁻¹ ≤ c * (1 + ε) := fun ε h0 h1 =>
    le_of_tendsto hlim' ((pinch ε h0 h1).mono fun _ h => h.2)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) fun ε h => h
  have t1 : Tendsto (fun ε : ℝ => c * (1 - ε)) (𝓝[>] 0) (𝓝 c) := by
    have : Tendsto (fun ε : ℝ => c * (1 - ε)) (𝓝 0) (𝓝 (c * (1 - 0))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε : ℝ => c * (1 + ε)) (𝓝[>] 0) (𝓝 c) := by
    have : Tendsto (fun ε : ℝ => c * (1 + ε)) (𝓝 0) (𝓝 (c * (1 + 0))) :=
      (continuous_const.mul (continuous_const.add continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hcle : c ≤ (KVal X u')⁻¹ := le_of_tendsto t1 (hev.mono fun ε h => lo ε h.1 h.2)
  have hcge : (KVal X u')⁻¹ ≤ c := ge_of_tendsto t2 (hev.mono fun ε h => hi ε h.1 h.2)
  have hceq : c = (KVal X u')⁻¹ := le_antisymm hcle hcge
  rw [← ENNReal.ofReal_toReal hc₀, ← hc, hceq, ENNReal.ofReal_inv_of_pos hK0]

def SplitAsymFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)) (p : ℕ → ℝ),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤ ∧ 0 < p n) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (X.measG.μGinf (TubeG X u' (V n))).toReal / p n) atTop
        (𝓝 (Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F))) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal / (p n * (νinf (W n)).toReal)) atTop
        (𝓝 (Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F))))

theorem locRatioFor_of {Pr : ChartPred} (hK : KPos) (hS : SplitAsymFor Pr) : LocRatioFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  obtain ⟨V, W, p, hVW, hsh, hG, hTup⟩ := hS X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  refine ⟨V, W, fun n => ?_, hsh, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hVW n
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  set g0 : ℝ := Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F)
    with hg0
  set t0 : ℝ := Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) with ht0
  have hKe : KVal X u' = g0 * t0⁻¹ := by
    simp only [KVal, hg0, ht0, zpow_neg, zpow_natCast]
  have hg0ne : g0 ≠ 0 := by
    intro h; rw [hKe, h, zero_mul] at hK0; exact lt_irrefl _ hK0
  have ht0ne : t0 ≠ 0 := by
    intro h; rw [hKe, h, inv_zero, mul_zero] at hK0; exact lt_irrefl _ hK0
  have hlim := hTup.div hG hg0ne
  have hval : t0 / g0 = (KVal X u')⁻¹ := by
    rw [hKe, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  rw [hval] at hlim
  refine hlim.congr fun n => ?_
  obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt, hp⟩ := hVW n
  have hBr : 0 < (νinf (W n)).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have hMr : 0 < (X.measG.μGinf (TubeG X u' (V n))).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
  simp only [Pi.div_apply]
  field_simp

def TrivialChartCondition : ChartPred := fun _ _ _ _ _ _ => True

theorem jacOne_of (hK : KPos) (hR : LocRatio) : JacOne := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC J hJ1 hJc Ω₂ hΩ₂ hΩ₂n c₀ hid
  exact jacOneFor_of (Pr := TrivialChartCondition) hK
    (fun X u' ψ hT μinf νinf fibInf hP Ω a hC _ => hR X u' ψ hT μinf νinf fibInf hP Ω a hC)
    X u' ψ hT μinf νinf fibInf hP Ω a hC trivial J hJ1 hJc Ω₂ hΩ₂ hΩ₂n c₀ hid

end PI.AprimeInfW
