import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ImgLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def gVal {D : D7} (X : HidaSetting D) : ℝ :=
  Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F)

def tVal {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : ℝ :=
  Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F))

def GrpLim {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  (∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → MeasurableSet (TubeG X u' (κ '' ball 0 ρ)) ∧
      0 < X.measG.μGinf (TubeG X u' (κ '' ball 0 ρ)) ∧ X.measG.μGinf (TubeG X u' (κ '' ball 0 ρ)) < ⊤) ∧
  ∀ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) → Tendsto ρ atTop (𝓝 0) →
    Tendsto (fun n => (X.measG.μGinf (TubeG X u' (κ '' ball 0 (ρ n)))).toReal /
      (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal) atTop (𝓝 (gVal X))

def PsiM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η : Type}
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
  eT (κ z.1 • rmulT X (a (eH.symm z.2)) (Y0 X u'))

def TupJac {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (μinf : Measure (TupI X)) (νinf : Measure (HmI X)) (a : HmI X → MfI X) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η) (eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cμ cν : ℝ)
    (Ψ' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)),
    0 < cμ ∧ 0 < cν ∧ μinf.map eT = ENNReal.ofReal cμ • volume ∧ νinf.map eH = ENNReal.ofReal cν • volume ∧
    U ∈ 𝓝 ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) ∧
    (∀ z ∈ U, HasFDerivWithinAt (PsiM X u' a κ eT eH) (Ψ' z) U z) ∧ Set.InjOn (PsiM X u' a κ eT eH) U ∧
    ContinuousAt (fun z => |(Ψ' z).det|) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) ∧
    (∀ᶠ T in 𝓝 (TI X u' hT), IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X) ∧
    cμ * |(Ψ' ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT))).det| / cν = tVal X u'

def GoodP : ChartPred := fun X u' hT μinf νinf a =>
  ∃ (ι : Type) (_ : Fintype ι) (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
    GrpLim X u' κ ∧ TupJac X u' hT μinf νinf a κ

theorem splitAsym_good : SplitAsymFor GoodP := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  obtain ⟨ι, hι, κ, ⟨⟨ρ0, hρ0, hG0⟩, hGl⟩, η, hη, eT, eH, cμ, cν, Ψ', U, hcμ, hcν, hμ, hν, hU, hΨ', hinj,
    hdet, hev, harith⟩ := hPr
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : BorelSpace (HmI X) := ⟨rfl⟩
  haveI hHaar : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  set T0 := TI X u' hT with hT0
  set z0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η := (0, eH T0) with hz0
  set Ψ := PsiM X u' a κ eT eH with hΨ
  set d := |(Ψ' z0).det| with hd

  have hdet1 : (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∈ 𝓝 z0 := hdet (Iio_mem_nhds (by linarith))
  have hHn : eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X}) ∈ 𝓝 (eH T0) := by
    apply eH.symm.continuous.continuousAt.preimage_mem_nhds
    rw [eH.symm_apply_apply]
    exact inter_mem hΩ₂n hev
  have hS : U ∩ (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∩
      Prod.snd ⁻¹' (eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X})) ∈ 𝓝 z0 :=
    inter_mem (inter_mem hU hdet1) (continuous_snd.continuousAt.preimage_mem_nhds hHn)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.1 hS
  set m0 := min r ρ0 with hm0
  have hm0p : 0 < m0 := lt_min hr hρ0
  set ρ : ℕ → ℝ := fun n => m0 / ((n : ℝ) + 2) with hρ
  have hρp : ∀ n, 0 < ρ n := fun n => div_pos hm0p (by positivity)
  have hρle : ∀ n, ρ n < m0 := fun n => by
    show m0 / ((n : ℝ) + 2) < m0
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hρr : ∀ n, ρ n < r := fun n => (hρle n).trans_le (min_le_left _ _)
  have hρ0' : ∀ n, ρ n < ρ0 := fun n => (hρle n).trans_le (min_le_right _ _)
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat m0).comp (tendsto_add_atTop_nat 2)
    refine h1.congr fun n => ?_
    simp only [Function.comp, hρ, Nat.cast_add, Nat.cast_ofNat]

  set A : ℕ → Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) := fun n => ball 0 (ρ n) ×ˢ ball (eH T0) (ρ n) with hA
  have hAb : ∀ n, A n = ball z0 (ρ n) := fun n => ball_prod_same _ _ _
  have hAS : ∀ n, A n ⊆ U ∩ (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∩
      Prod.snd ⁻¹' (eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X})) := fun n => by
    rw [hAb n]; exact (ball_subset_ball (hρr n).le).trans hrS
  have hAU : ∀ n, A n ⊆ U := fun n z hz => (hAS n hz).1.1
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by rw [hAb n]; exact measurableSet_ball
  set V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := fun n => κ '' ball 0 (ρ n) with hV
  set W : ℕ → Set (HmI X) := fun n => eH ⁻¹' ball (eH T0) (ρ n) with hW
  have hWp : ∀ n, ∀ T ∈ W n, T ∈ Ω₂ ∧ IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X := by
    intro n T hTW
    have h1 := (hAS n (show ((0 : EuclideanSpace ℝ ι), eH T) ∈ A n from ⟨mem_ball_self (hρp n), hTW⟩)).2
    simpa [eH.symm_apply_apply] using h1
  have hΨc : ∀ n, ContinuousOn Ψ (A n) := fun n z hz =>
    ((hΨ' z (hAU n hz)).mono (hAU n)).continuousWithinAt
  have hΨm : ∀ n, MeasurableSet (Ψ '' A n) := fun n =>
    (hAm n).image_of_continuousOn_injOn (hΨc n) (hinj.mono (hAU n))
  have hBox : ∀ n, BoxT X u' a (V n) (W n) = eT ⁻¹' (Ψ '' A n) := by
    intro n
    ext y
    constructor
    · rintro ⟨T, hTW, g, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(x, eH T), ⟨hx, hTW⟩, ?_⟩
      simp [hΨ, PsiM, eH.symm_apply_apply]
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, hy⟩
      refine ⟨eH.symm t, ?_, κ x, ⟨x, hx, rfl⟩, ?_⟩
      · show eH (eH.symm t) ∈ ball (eH T0) (ρ n)
        rw [eH.apply_symm_apply]; exact ht
      · apply eT.injective
        rw [← hy]
        rfl
  have hvolΨ : ∀ n, volume (Ψ '' A n) = ∫⁻ z in A n, ENNReal.ofReal |(Ψ' z).det| := fun n =>
    (lintegral_abs_det_fderiv_eq_addHaar_image volume (hAm n)
      (fun z hz => (hΨ' z (hAU n hz)).mono (hAU n)) (hinj.mono (hAU n))).symm
  have hvolA : ∀ n, volume (A n) = volume (ball (0 : EuclideanSpace ℝ ι) (ρ n)) * volume (ball (eH T0) (ρ n)) :=
    fun n => by rw [Measure.volume_eq_prod, Measure.prod_prod]
  have hAt : ∀ n, volume (A n) < ⊤ := fun n => by rw [hAb n]; exact measure_ball_lt_top
  have hA0 : ∀ n, 0 < volume (A n) := fun n => by rw [hAb n]; exact measure_ball_pos _ _ (hρp n)
  have hΨt : ∀ n, volume (Ψ '' A n) < ⊤ := by
    intro n
    rw [hvolΨ n]
    calc ∫⁻ z in A n, ENNReal.ofReal |(Ψ' z).det| ≤ ∫⁻ _ in A n, ENNReal.ofReal (d + 1) :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun z hz =>
            ENNReal.ofReal_le_ofReal (le_of_lt (hAS n hz).1.2)))
      _ = ENNReal.ofReal (d + 1) * volume (A n) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hAt n)
  have hμB : ∀ n, μinf (BoxT X u' a (V n) (W n)) = ENNReal.ofReal cμ * volume (Ψ '' A n) := fun n => by
    rw [hBox n, ← Measure.map_apply eT.continuous.measurable (hΨm n), hμ, Measure.smul_apply, smul_eq_mul]
  have hνW : ∀ n, νinf (W n) = ENNReal.ofReal cν * volume (ball (eH T0) (ρ n)) := fun n => by
    rw [hW, ← Measure.map_apply eH.continuous.measurable measurableSet_ball, hν, Measure.smul_apply, smul_eq_mul]
  have hBy0 : ∀ n, 0 < volume (ball (eH T0) (ρ n)) := fun n => measure_ball_pos _ _ (hρp n)
  have hBx0 : ∀ n, 0 < volume (ball (0 : EuclideanSpace ℝ ι) (ρ n)) := fun n => measure_ball_pos _ _ (hρp n)
  refine ⟨V, W, fun n => (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal, fun n => ?_, ?_, ?_, ?_⟩
  · obtain ⟨g1, g2, g3⟩ := hG0 (ρ n) (hρp n) (hρ0' n)
    refine ⟨measurableSet_ball.preimage eH.continuous.measurable, fun T hT' => (hWp n T hT').1, ?_, ?_,
      fun T hT' => (hWp n T hT').2.1, ?_, ?_, ?_, g1, g2, g3, ENNReal.toReal_pos (hBx0 n).ne' measure_ball_lt_top.ne⟩
    · rw [hνW n]; exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hcν).ne' (hBy0 n).ne'
    · rw [hνW n]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
    · rw [hBox n]; exact eT.continuous.measurable (hΨm n)
    · rintro y ⟨T, hTW, g, -, rfl⟩
      exact indI_smul X g _ (hWp n T hTW).2.2
    · rw [hμB n]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hΨt n)
  · intro U' hU'
    have h1 : eH.symm ⁻¹' U' ∈ 𝓝 (eH T0) := by
      apply eH.symm.continuous.continuousAt.preimage_mem_nhds
      rw [eH.symm_apply_apply]; exact hU'
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 h1
    filter_upwards [hρlim.eventually (gt_mem_nhds hε)] with n hn
    intro T hTW
    have h2 : eH T ∈ ball (eH T0) ε := ball_subset_ball hn.le hTW
    have h3 := hεs h2
    simpa [eH.symm_apply_apply] using h3
  · exact hGl ρ hρp hρlim
  · have hi := img_ratio (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) hΨ' hinj hdet A hAm hAU
      hA0 hAt (fun V' hV' => by
        obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hV'
        filter_upwards [hρlim.eventually (gt_mem_nhds hε)] with n hn
        rw [hAb n]; exact (ball_subset_ball hn.le).trans hεs)
    have hval : cμ / cν * d = tVal X u' := by rw [← harith]; ring
    change Tendsto _ atTop (𝓝 (tVal X u'))
    rw [← hval]
    refine (hi.const_mul (cμ / cν)).congr fun n => ?_
    have hx : 0 < (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal :=
      ENNReal.toReal_pos (hBx0 n).ne' measure_ball_lt_top.ne
    have hy : 0 < (volume (ball (eH T0) (ρ n))).toReal := ENNReal.toReal_pos (hBy0 n).ne' measure_ball_lt_top.ne
    rw [hμB n, hνW n, hvolA n, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hcμ.le, ENNReal.toReal_ofReal hcν.le]
    field_simp

theorem jacOneGood (hK : KPos) : JacOneFor GoodP :=
  jacOneFor_of hK (locRatioFor_of hK splitAsym_good)

end PI.AprimeInfW
