import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPshLocal

namespace GlobalTheory.CompanionTheory.AnForm.PshLocal

open Filter Topology ReciprocityTheory.AnForm.A

theorem isPsh_mono {n : ℕ} {V W : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (hWV : W ⊆ V)
    (h : IsPsh V φ) : IsPsh W φ := by
  unfold ReciprocityTheory.AnForm.A.IsPsh at h ⊢
  obtain ⟨hu, hm⟩ := h
  exact ⟨hu.mono hWV, fun z w hzw => hm z w fun ζ hζ => hWV (hzw ζ hζ)⟩

theorem isPsh_of_locally :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U →
      (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) →
      ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro n U φ hU hloc
  have hloc' : ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ := by
    intro p hp
    obtain ⟨V, hV, hpV, hψ⟩ := hloc p hp
    exact ⟨V ∩ U, hV.inter hU, ⟨hpV, hp⟩, Set.inter_subset_right, isPsh_mono Set.inter_subset_left hψ⟩
  have hlocg : ∀ k : ℕ, ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      IsPsh W (fun x => max (φ x) (-(k : ℝ))) := by
    intro k p hp
    obtain ⟨W, hW, hpW, hWU, hψ⟩ := hloc' p hp
    exact ⟨W, hW, hpW, hWU, GroundTheory.Heights₂.Heights.NineStatements.PshLocal.isPsh_max hψ _⟩
  have husc := GroundTheory.Heights₂.Heights.NineStatements.PshLocal.usc hloc'
  unfold ReciprocityTheory.AnForm.A.IsPsh
  refine ⟨husc, ?_⟩
  intro z w hzw
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let F : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w)
  let f : ℕ → ℝ → ℝ := fun k θ => max (F θ) (-(k : ℝ))
  have hcore : ∀ k : ℕ, IntervalIntegrable (f k) MeasureTheory.volume 0 (2 * Real.pi) ∧
      max (φ z) (-(k : ℝ)) ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f k θ := fun k =>
    GroundTheory.Heights₂.Heights.NineStatements.PshLocal.core hU (hlocg k) z w hzw (c := -(k : ℝ))
      (fun θ => le_max_right _ _)
  have hint : ∀ k, MeasureTheory.Integrable (f k) μ := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp (hcore k).1
  have hanti : ∀ θ, Antitone fun k : ℕ => f k θ := by
    intro θ
    refine antitone_nat_of_succ_le fun k => ?_
    show max (F θ) (-(((k + 1 : ℕ)) : ℝ)) ≤ max (F θ) (-(k : ℝ))
    push_cast
    exact max_le_max le_rfl (by linarith)
  have htend : ∀ θ, Tendsto (fun k : ℕ => f k θ) atTop (𝓝 (F θ)) := by
    intro θ
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈-F θ⌉₊) fun k hk => ?_
    have hc := Nat.le_ceil (-F θ)
    have hk' : ((⌈-F θ⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    exact max_eq_left (by linarith)
  have hlow : ∀ k : ℕ, 2 * Real.pi * φ z ≤ ∫ θ, f k θ ∂μ := by
    intro k
    have h1 := le_trans (le_max_left (φ z) (-(k : ℝ))) (hcore k).2
    rw [intervalIntegral.integral_of_le h2π] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 h2π
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at h3
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).aestronglyMeasurable)
      (Filter.Eventually.of_forall htend)
  have hGnn : ∀ (k : ℕ) θ, 0 ≤ f 0 θ - f k θ := fun k θ => sub_nonneg.mpr (hanti θ (Nat.zero_le k))
  have hFle : ∀ θ, F θ ≤ f 0 θ := fun θ => le_max_left _ _
  have hGint : MeasureTheory.Integrable (fun θ => f 0 θ - F θ) μ := by
    refine ⟨(hint 0).aestronglyMeasurable.sub hFmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => sub_nonneg.mpr (hFle θ))]
    have hlim : ∀ θ, Tendsto (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop
        (𝓝 (ENNReal.ofReal (f 0 θ - F θ))) :=
      fun θ => (ENNReal.continuous_ofReal.tendsto _).comp ((htend θ).const_sub _)
    have hterm : ∀ k : ℕ, ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ ≤
        ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) := by
      intro k
      have e := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun θ => f 0 θ - f k θ)
        ((hint 0).sub (hint k)) (Filter.Eventually.of_forall (hGnn k))
      rw [← e, MeasureTheory.integral_sub (hint 0) (hint k)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hlow k])
    calc ∫⁻ θ, ENNReal.ofReal (f 0 θ - F θ) ∂μ
        = ∫⁻ θ, liminf (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop ∂μ := by
          congr 1
          funext θ
          exact ((hlim θ).liminf_eq).symm
      _ ≤ liminf (fun k : ℕ => ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ) atTop :=
          MeasureTheory.lintegral_liminf_le' fun k => ((hint 0).sub (hint k)).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hterm)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hFint : MeasureTheory.Integrable F μ :=
    ((hint 0).sub hGint).congr (Filter.Eventually.of_forall fun θ => by simp)
  have hlimI := MeasureTheory.integral_tendsto_of_tendsto_of_antitone hint hFint
    (Filter.Eventually.of_forall hanti) (Filter.Eventually.of_forall htend)
  have hge : 2 * Real.pi * φ z ≤ ∫ θ, F θ ∂μ := ge_of_tendsto' hlimI hlow
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mpr hFint, ?_⟩
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h2π]
  have h4 := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr h2π)
  rwa [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at h4

end GlobalTheory.CompanionTheory.AnForm.PshLocal
