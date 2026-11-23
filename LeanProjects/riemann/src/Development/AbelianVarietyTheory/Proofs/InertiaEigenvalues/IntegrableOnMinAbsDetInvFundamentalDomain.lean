import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

noncomputable section

open GlobalTheory.UnitaryBC

namespace GlobalTheory.FinVolGL

theorem exists_tsum_min_le {T : ℝ} (hT : 1 < T) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, ENNReal.ofReal (min (T ^ n * u) (T ^ n * u)⁻¹) ≤ B := by
  have hT0 : 0 < T := one_pos.trans hT
  have hq0 : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
  have hq : T⁻¹ < 1 := inv_lt_one_of_one_lt₀ hT
  have hsum : Summable fun k : ℤ => T * T⁻¹ ^ k.natAbs :=
    (Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one hq0 hq)
      (by simpa using summable_geometric_of_lt_one hq0 hq)).mul_left T
  refine ⟨∑' k : ℤ, ENNReal.ofReal (T * T⁻¹ ^ k.natAbs), hsum.tsum_ofReal_ne_top, fun u hu => ?_⟩
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow hu hT
  rw [← (Equiv.subRight m).tsum_eq]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  rw [Equiv.subRight_apply]
  have hp : 0 < T ^ (k - m) := zpow_pos hT0 _
  have e1 : T ^ (k - m) * T ^ m = T ^ k := by rw [← zpow_add₀ hT0.ne', sub_add_cancel]
  have e2 : T ^ (k - m) * T ^ (m + 1) = T ^ (k + 1) := by
    rw [← zpow_add₀ hT0.ne']; congr 1; ring
  have hv1 : T ^ k ≤ T ^ (k - m) * u := e1 ▸ mul_le_mul_of_nonneg_left h1 hp.le
  have hv2 : T ^ (k - m) * u < T ^ (k + 1) := e2 ▸ mul_lt_mul_of_pos_left h2 hp
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · refine (min_le_right _ _).trans ?_
    have h3 := inv_anti₀ (zpow_pos hT0 _) hv1
    rw [zpow_natCast, ← inv_pow] at h3
    rw [Int.natAbs_natCast]
    exact h3.trans (le_mul_of_one_le_left (pow_nonneg hq0 _) hT.le)
  · refine (min_le_left _ _).trans (hv2.le.trans (le_of_eq ?_))
    rw [zpow_add_one₀ hT0.ne', _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, inv_pow, mul_comm]

theorem integrableOn_min_absDet : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hc : Continuous fun g => min (δ g) (δ g)⁻¹ := hδc.min (hδc.inv₀ fun g => (hδ0 g).ne')
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (.of_forall fun g => le_min (hδ0 g).le (inv_nonneg.2 (hδ0 g).le))).2 ?_⟩
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
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 (fun g => ENNReal.ofReal (min (δ g) (δ g)⁻¹))
    (by rintro _ ⟨γ, rfl⟩ g; simp only [hδr])
    hc.measurable.ennreal_ofReal.aemeasurable]
  obtain ⟨B, hB, h⟩ := exists_tsum_min_le hT1
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

example : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := integrableOn_min_absDet

end GlobalTheory.FinVolGL
