import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace AdmissibleVectors

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem map_wd (μ : Measure (GA E k)) [μ.IsHaarMeasure] (β : GA E k → ℝ≥0∞) (t : GA E k) :
    Measure.map (MeasurableEquiv.mulLeft t⁻¹) (μ.withDensity β) = μ.withDensity fun g => β (t * g) := by
  ext s hs
  rw [Measure.map_apply (MeasurableEquiv.mulLeft t⁻¹).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), ← lintegral_indicator hs]
  rw [← lintegral_mul_left_eq_self (μ := μ) _ t]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

end AdmissibleVectors

open AdmissibleVectors in
set_option synthInstance.maxHeartbeats 400000 in
theorem sum_wt_mul_massS_le_inv_pow_mul_total_mass : Q1 → Q2 → N2 → N3 → C1 := by
  intro _ hQ2 hN2 hN3 E _ _ _ k μ _ hk β hβ w l Φ hΦ hΦu hint
  set t := fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) with ht
  obtain ⟨hsf, hinv, -⟩ := (hN3 E k).1 0 (by omega)
  have := hsf
  obtain ⟨hUU, -⟩ := (hN3 E k).2.2.2 hk
  have hq0 : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set c : ℝ≥0∞ := ENNReal.ofReal ((Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l) with hc
  have hcpos : 0 < (Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l :=
    zpow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hq0)) _
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hcpos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ0m : Measurable fun g => β (t * g) := hβ.1.comp (measurable_const_mul t)
  set β' : GA E k → ℝ≥0∞ := fun g => c⁻¹ * β (t * g) with hβ'
  have hβ'm : Measurable β' := hβ0m.const_mul _
  have hwt : IsWt (nuP E k 0) β' := by
    refine ⟨hβ'm, fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_const_mul c⁻¹ (f := fun h => β (t * (h * g))) (hβ0m.comp (measurable_mul_const g))]
    have := hN2 E k w l (fun h => β (h * (t * g))) (hβ.1.comp (measurable_mul_const _))
    rw [← ht] at this
    simp only [mul_assoc, inv_mul_cancel_left] at this
    rw [this, hβ.2 (t * g), mul_one, ENNReal.inv_mul_cancel hc0 hctop]

  have hH : ∀ᵐ h ∂nuP E k 0, h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)} := by
    set A := {h : GA E k | ¬ UU 0 h}
    have hA : nuP E k 0 A = 0 := ae_iff.1 hUU
    set S := toMeasurable (nuP E k 0) A
    have hS : MeasurableSet S := measurableSet_toMeasurable _ _
    have hS0 : nuP E k 0 S = 0 := by rw [measure_toMeasurable]; exact hA
    have hcm : Measurable fun h : GA E k => t * h * t⁻¹ := (measurable_const_mul t).mul_const _
    have := hN2 E k w l (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS, hS0, mul_zero] at this
    have h2 := (lintegral_eq_zero_iff ((measurable_one.indicator hS).comp hcm)).1 this
    filter_upwards [h2] with h hh
    by_contra hn
    have : t * h * t⁻¹ ∈ S := subset_toMeasurable _ _ hn
    simp [Set.indicator_of_mem this] at hh
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k 0 ∂Measure.dirac (1 : GA E k) = 1 := fun g => by
    rw [lintegral_dirac]; simpa using hβ.2 g
  have hΦ'm : Measurable fun g => Φ (t * g) := hΦ.comp (measurable_const_mul t)
  have hΦ'H : ∀ h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)}, ∀ g, Φ (t * (h * g)) = Φ (t * g) := by
    intro h hh g
    have := hΦu _ hh (t * g)
    simpa [mul_assoc] using this
  have hmap := map_wd μ β t
  have hsm : μ.withDensity (fun g => β (t * g)) = c • μ.withDensity β' := by
    rw [← withDensity_smul _ hβ'm]
    congr 1
    funext g
    simp only [hβ', Pi.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
  have hint0 : Integrable (fun g => Φ (t * g)) (μ.withDensity fun g => β (t * g)) := by
    rw [← hmap, integrable_map_equiv]
    simpa [Function.comp_def] using hint
  have hint' : Integrable (fun g => Φ (t * g)) (μ.withDensity β') := by
    have h1 : μ.withDensity β' = c⁻¹ • μ.withDensity (fun g => β (t * g)) := by
      rw [hsm, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
    rw [h1]
    exact hint0.smul_measure (ENNReal.inv_ne_top.2 hc0)
  have hQ := hQ2 (GA E k) μ (nuP E k 0) (Measure.dirac 1) _ β' β hinv hH hwt hβ.1 hone
    (fun g => Φ (t * g)) hΦ'm hΦ'H hint'
  simp only [integral_dirac, one_mul] at hQ
  refine ⟨hQ.1, ?_⟩
  have e1 : ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ (t * g) ∂μ.withDensity fun g => β (t * g) := by
    rw [← hmap, integral_map_equiv]
    simp [MeasurableEquiv.coe_mulLeft]
  rw [e1, hsm, integral_smul_measure, hQ.2, hc, ENNReal.toReal_ofReal hcpos.le, Complex.real_smul]
  push_cast
  rfl

end PositivityTheory.AdelicQuotientData

end
