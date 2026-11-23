import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open GlobalTheory.UnitaryBC GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ContDiff ENNReal

namespace GlobalTheory.RSThetaLow

theorem exists_tsum_zpow_le_low {T s : ℝ} (hT : 1 < T) (hs : 0 < s) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, (if T ^ n * u ≤ 1 then ENNReal.ofReal ((T ^ n * u) ^ s) else 0) ≤ B := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.RSTheta.exists_tsum_zpow_le hT hs
  refine ⟨B, hB, fun u hu => ?_⟩
  have hT0 : 0 < T := one_pos.trans hT
  refine le_of_eq_of_le ?_ (h u⁻¹ (inv_pos.2 hu))
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply]
  have hp : 0 < T ^ n * u⁻¹ := by positivity
  have e : T ^ (-n) * u = (T ^ n * u⁻¹)⁻¹ := by
    rw [_root_.zpow_neg, mul_inv, inv_inv]
  rw [e, Real.inv_rpow hp.le, Real.rpow_neg hp.le]
  simp only [inv_le_one₀ hp]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem integrableOn_absDet_rpow (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s)
      (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hm : MeasurableSet {g | δ g ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hc : Continuous fun g => δ g ^ s := hδc.rpow_const fun g => Or.inl (hδ0 g).ne'
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall fun g => Real.rpow_nonneg (hδ0 g).le _)).2 ?_⟩
  rw [Set.inter_comm, ← Measure.restrict_restrict hm, ← lintegral_indicator hm]
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => splitCentre E a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 _
    (by rintro _ ⟨γ, rfl⟩ g; simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [show δ (ratGL E a γ * g) = δ g from hδr γ g])
    ((hc.measurable.ennreal_ofReal.indicator hm).aemeasurable)]
  obtain ⟨B, hB, h⟩ := exists_tsum_zpow_le_low hT1 hs
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

theorem integrableOn_absDet_rpow_low : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    ∀ s : ℝ, 0 < s → IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s)
      (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ :=
  fun _ _ _ _ _ ha μ _ _ h𝓕 _ hs => integrableOn_absDet_rpow ha μ h𝓕 hs

end GlobalTheory.RSThetaLow

end
