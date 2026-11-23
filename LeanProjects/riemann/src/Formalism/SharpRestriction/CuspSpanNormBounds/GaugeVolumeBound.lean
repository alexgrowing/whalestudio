import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeVolRatio
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative

noncomputable section

namespace Formalism.MainNotions.FundamentalDomainUnfolding

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.BridgeVolRatio
open scoped ENNReal

def GamY (I : AutInst) (y : I.Gf) : Set I.GA := {γ | γ ∈ I.GFset ∧ y⁻¹ * γ.2 * y ∈ I.Kset}

def IsFundInf (I : AutInst) (y : I.Gf) (μ : Measure I.Ginf) (D : Set I.Ginf) : Prop :=
  MeasurableSet D ∧ (∀ z : I.Ginf, ∃ γ ∈ GamY I y, γ.1 * z ∈ D) ∧
    ∀ γ ∈ GamY I y, γ ≠ 1 → μ ((fun z => γ.1 * z) '' D ∩ D) = 0

def muInf (I : AutInst) : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)

def ClassReps (I : AutInst) (ys : Finset I.Gf) : Prop :=
  (∀ x : I.Gf, ∃ γ ∈ I.GFset, ∃ y ∈ ys, ∃ k ∈ I.Kset, x = γ.2 * y * k) ∧
    ∀ y ∈ ys, ∀ y' ∈ ys, (∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, y' = γ.2 * y * k) → y = y'

def UnfoldVol : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∃ ys : Finset I.Gf, ClassReps I ys ∧
      (∃ D : I.Gf → Set I.Ginf, ∀ y ∈ ys, IsFundInf I y (muInf I) (D y)) ∧
      ∀ D : I.Gf → Set I.Ginf, (∀ y ∈ ys, IsFundInf I y (muInf I) (D y)) →
        I.muA μf fund = μf I.Kset * ∑ y ∈ ys, muInf I (D y)

def FundInfExists : Prop := ∀ (I : AutInst) (y : I.Gf), ∃ D : Set I.Ginf, IsFundInf I y (muInf I) D

def CovolSum (X : CData) (R : ℝ) : Prop :=
  ∀ (ys : Finset X.I.Gf) (D : X.I.Gf → Set X.I.Ginf), ClassReps X.I ys →
    (∀ y ∈ ys, IsFundInf X.I y (muInf X.I) (D y)) →
    ∑ y ∈ ys, muInf X.I (D y) ≤ ENNReal.ofReal (X.I.gaugeU * R)

theorem gauge_volume_bound_of_parts (hU : UnfoldVol) (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) (X : CData) {n₀ : ℕ} {A C0 R : ℝ}
    (hX : X.HypB n₀ A) (hR0 : 0 ≤ R) (hB : CovolSum X R)
    (hR : R ≤ cn_Y X ^ (C0 * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) : GaugeVolumeBoundVar X C0 := by
  obtain ⟨hH, hF, -⟩ := RegData_of_HypB X hX
  have hμ : X.μf.IsHaarMeasure := hH
  obtain ⟨ys, hys, ⟨D, hD⟩, heq⟩ := hU X.I X.μf X.fund hF
  have hU0 : 0 < X.I.gaugeU := Finset.prod_pos fun v _ => (hGD _ (X.I.ε v)).2
  have hsum := hB ys D hys hD
  have hvol := heq D hD
  obtain ⟨hpos1, hKfin⟩ := kg_pos_fin X hμ (le_refl 1)
  have hKpos : 0 < X.μf X.I.Kset := lt_of_lt_of_le hpos1 (measure_mono (kg_sub X.I 1))
  set μK := (X.μf X.I.Kset).toReal with hμK
  have hμK0 : 0 < μK := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have huR : 0 ≤ X.I.gaugeU * R := mul_nonneg hU0.le hR0
  have hle : X.I.vol X.μf X.fund ≤ μK * (X.I.gaugeU * R) := by
    unfold AutInst.vol
    rw [hvol]
    calc (X.μf X.I.Kset * ∑ y ∈ ys, muInf X.I (D y)).toReal
        ≤ (X.μf X.I.Kset * ENNReal.ofReal (X.I.gaugeU * R)).toReal := by
          refine ENNReal.toReal_mono (ENNReal.mul_ne_top hKfin.ne ENNReal.ofReal_ne_top) ?_
          gcongr
      _ = μK * (X.I.gaugeU * R) := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal huR]
  unfold GaugeVolumeBoundVar
  have hp : 0 < μK * X.I.gaugeU := mul_pos hμK0 hU0
  calc X.I.vol X.μf X.fund / (μK * X.I.gaugeU) ≤ μK * (X.I.gaugeU * R) / (μK * X.I.gaugeU) :=
        div_le_div_of_nonneg_right hle hp.le
    _ = R := by field_simp
    _ ≤ _ := hR

end Formalism.MainNotions.FundamentalDomainUnfolding

end
