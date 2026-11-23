import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem restrict_Dt_two_null {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) : (μ.restrict 𝓕) {g | Dt g ∈ ({2} : Set ℝ)} = 0 := by
  obtain ⟨h1, hz, hT⟩ := hG μ 𝓕 mK 𝓓 h0
  obtain ⟨z, hz2, -⟩ := hz 2 (by norm_num)
  have hinv := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1
  have hS : MeasurableSet {g : G2 | Dt g ∈ ({2} : Set ℝ)} := measurable_Dt (measurableSet_singleton _)
  have hS1 : MeasurableSet {g : G2 | Dt g = 1} := measurable_Dt (measurableSet_singleton (1 : ℝ))
  have key := hinv (Set.indicator {g : G2 | Dt g ∈ ({2} : Set ℝ)} (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hS) (linv_ind (fun _ _ => rfl) _)
  have e1 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ ({2} : Set ℝ)} (fun _ => (1 : ℝ≥0∞)) (dg2 z z * g))
      = Set.indicator {g : G2 | Dt g = 1} (fun _ => (1 : ℝ≥0∞)) := by
    funext g
    have : (dg2 z z * g ∈ {g : G2 | Dt g ∈ ({2} : Set ℝ)}) ↔ g ∈ {g : G2 | Dt g = 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Dt_dg, hz2]
      constructor <;> intro h <;> linarith
    by_cases hg : g ∈ {g : G2 | Dt g = 1}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (this.2 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (this.1 h))]
  rw [e1, lintegral_indicator_const hS1, lintegral_indicator_const hS, one_mul, one_mul] at key
  rw [← key]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans h1.le) bot_le

theorem Bd_reflect : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
    Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
      GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
  intro μ 𝓕 mK 𝓓 H c hG h0 hH hc s
  have hnull2 := restrict_Dt_two_null hG h0
  obtain ⟨h1, hz, hT⟩ := hG μ 𝓕 mK 𝓓 h0
  obtain ⟨z, hz2, hzc⟩ := hz (1 / 2) (by norm_num)
  have hzc := hzc c hc
  set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw
  set w' : G2 → ℂ := fun g => H g * cdet c⁻¹ g * ((Dt g : ℝ) : ℂ) ^ (-s) with hw'
  have mS : ∀ A : Set ℝ, MeasurableSet A → MeasurableSet {g : G2 | Dt g ∈ A} := fun A hA => measurable_Dt hA
  have hband : band = {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} := rfl
  have mB : MeasurableSet band := hband ▸ mS _ measurableSet_Ico

  have b1 : Bd μ 𝓕 H c⁻¹ (-s) = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w' g ∂μ := by
    rw [setIntegral_indicator (mS _ measurableSet_Ico)]; rfl
  have b2 : Bd μ 𝓕 H c s = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w g ∂μ := by
    rw [setIntegral_indicator (mS _ measurableSet_Ico)]; rfl

  have r1 := (hT Ad3.R.inv2 (Or.inl rfl)).2 (Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w')
    ((measurable_w hH c⁻¹ (-s)).indicator (mS _ measurableSet_Ico)) (linv_ind (linv_w hH c⁻¹ (-s)) _)
  have e1 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w' (Ad3.R.inv2 g))
      = Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w := by
    funext g
    have hp := Dt_pos g
    have hm : (Ad3.R.inv2 g ∈ {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2}) ↔ g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioc, module_det_inverse_twist]
      rw [one_le_inv₀ hp, inv_lt_comm₀ hp (by norm_num)]
      constructor
      · rintro ⟨a, b⟩; exact ⟨by norm_num at b ⊢; linarith, a⟩
      · rintro ⟨a, b⟩; exact ⟨b, by norm_num at a ⊢; linarith⟩
    have hv : w' (Ad3.R.inv2 g) = w g := by
      simp only [hw, hw', Aut.inv2 hH, character_det_inverse_twist, module_cpow_det_inverse_twist, inv_inv, neg_neg]
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]

  have r2 := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2
    (Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w)
    ((measurable_w hH c s).indicator (mS _ measurableSet_Ioc)) (linv_ind (linv_w hH c s) _)
  have hhalf : (((1 / 2 : ℝ) : ℝ) : ℂ) ^ s = 2 ^ (-s) := by
    have : (((1 / 2 : ℝ) : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by push_cast; norm_num
    rw [this, Complex.inv_cpow _ _ (by simpa using Real.pi_pos.ne), Complex.cpow_neg]
  have e2 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w (dg2 z z * g))
      = fun g => 2 ^ (-s) * Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} w g := by
    funext g
    have hm : (dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1}) ↔ g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Dt_dg, hz2]
      constructor
      · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
    have hv : w (dg2 z z * g) = 2 ^ (-s) * w g := by
      simp only [hw]
      rw [hH.cen, cdet_dg c z hzc, cpow_dg, hz2, hhalf]
      ring
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]

  have ae1 : ∀ᵐ g ∂(μ.restrict 𝓕), Dt g ≠ 1 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h1)
  have ae2 : ∀ᵐ g ∂(μ.restrict 𝓕), Dt g ≠ 2 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull2
    simpa using this
  have r3 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} w g ∂μ
      = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w g ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae1, ae2] with g g1 g2
    have hm : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} ↔ g ∈ {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_Ico]
      constructor
      · rintro ⟨a, b⟩; exact ⟨a.le, lt_of_le_of_ne b g2⟩
      · rintro ⟨a, b⟩; exact ⟨lt_of_le_of_ne a (Ne.symm g1), b.le⟩
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.1 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.2 h))]
  rw [b1, b2, ← r1, e1, ← r2, e2, integral_const_mul, r3]

end GlobalTheory.CompanionTheory.RSZeta

end
