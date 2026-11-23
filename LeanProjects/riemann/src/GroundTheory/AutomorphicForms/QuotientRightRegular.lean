import Mathlib
import GroundTheory.AutomorphicForms.QuotientMeasure

open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

theorem compMeasurePreserving_congr {α : Type*} [MeasurableSpace α] {ν : Measure α} {p : ℝ≥0∞}
    {f f' : α → α} (h : f = f') (hf : MeasurePreserving f ν ν) (hf' : MeasurePreserving f' ν ν)
    (φ : Lp ℂ p ν) :
    Lp.compMeasurePreserving f hf φ = Lp.compMeasurePreserving f' hf' φ := by
  subst h
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant]

def rightTranslate (g : G) :
    Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ) where
  toLinearEquiv :=
    { Lp.compMeasurePreservingₗ ℂ (rightMul Γ g) (measurePreserving_rightMul μ g) with
      invFun := Lp.compMeasurePreservingₗ ℂ (rightMul Γ g⁻¹) (measurePreserving_rightMul μ g⁻¹)
      left_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, inv_mul_cancel, rightMul_one]
      right_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, mul_inv_cancel, rightMul_one] }
  norm_map' φ := Lp.norm_compMeasurePreserving φ _

theorem rightTranslate_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightTranslate Γ μ g φ =
      Lp.compMeasurePreserving (rightMul Γ g) (measurePreserving_rightMul μ g) φ :=
  rfl

theorem coeFn_rightTranslate (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightTranslate Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x ↦ φ (rightMul Γ g x) :=
  Lp.coeFn_compMeasurePreserving φ _

def rightRegular : G →* (Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) where
  toFun := rightTranslate Γ μ
  map_one' := by
    ext1 φ
    change Lp.compMeasurePreserving _ _ φ = φ
    rw [compMeasurePreserving_congr (rightMul_one Γ) _ (MeasurePreserving.id _),
      Lp.compMeasurePreserving_id_apply]
  map_mul' g h := by
    ext1 φ
    rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
    change Lp.compMeasurePreserving _ _ φ =
      Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact compMeasurePreserving_congr (rightMul_mul Γ g h) _ _ φ

@[simp]
theorem rightRegular_apply (g : G) : rightRegular Γ μ g = rightTranslate Γ μ g :=
  rfl

def rightRegularUnitary :
    G →* unitary (Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) :=
  (Unitary.linearIsometryEquiv (𝕜 := ℂ)).symm.toMonoidHom.comp (rightRegular Γ μ)

theorem rightRegularUnitary_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    (rightRegularUnitary Γ μ g : Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] _) φ = rightRegular Γ μ g φ :=
  rfl

theorem inner_rightRegular (g : G) (φ ψ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    inner ℂ (rightRegular Γ μ g φ) (rightRegular Γ μ g ψ) = inner ℂ φ ψ :=
  (rightRegular Γ μ g).inner_map_map φ ψ

section Continuity

variable [IsFiniteMeasureOnCompacts μ]

omit [μ.IsMulRightInvariant] in

theorem tendsto_lintegral_rightMul_sub {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 0) := by
  obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds g₀
  set K : Set (RightCosetSpace Γ) :=
    (fun p : RightCosetSpace Γ × G ↦ rightMul Γ p.2⁻¹ p.1) '' (tsupport ψ ×ˢ N) with hKdef
  have hK : IsCompact K := (hs.prod hN).image
    ((continuous_rightMul_prod Γ).comp (continuous_fst.prodMk continuous_snd.inv))
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  have hzero : ∀ g ∈ N, ∀ x ∉ K, ψ (rightMul Γ g x) = 0 := by
    intro g hg x hx
    by_contra h
    refine hx ⟨(rightMul Γ g x, g), ⟨subset_tsupport ψ h, hg⟩, ?_⟩
    change rightMul Γ g⁻¹ (rightMul Γ g x) = x
    rw [rightMul_rightMul, mul_inv_cancel, rightMul_one, id]
  have hg₀N : g₀ ∈ N := mem_of_mem_nhds hNn
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * M) ^ (2 : ℝ) with hc_def
  have hmeas : ∀ g, Measurable fun x ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
    fun g ↦ (((hc.comp (continuous_rightMul Γ g)).sub
      (hc.comp (continuous_rightMul Γ g₀))).measurable.enorm).pow_const _
  suffices key : Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂quotientMeasure Γ μ)) by
    rwa [lintegral_zero] at key
  refine tendsto_lintegral_filter_of_dominated_convergence (K.indicator fun _ ↦ c)
    (Eventually.of_forall hmeas) ?_ ?_ ?_
  · filter_upwards [hNn] with g hg
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖
          ≤ ‖ψ (rightMul Γ g x)‖ + ‖ψ (rightMul Γ g₀ x)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM (rightMul Γ g x), hM (rightMul Γ g₀ x)]
    · rw [hzero g hg x hx, hzero g₀ hg₀N x hx, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  · rw [lintegral_indicator_const hK.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hK.measure_lt_top.ne
  · refine Eventually.of_forall fun x ↦ ?_
    have hcont : Continuous fun g ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const).comp (continuous_enorm.comp
        ((hc.comp ((continuous_rightMul_prod Γ).comp
          (continuous_const.prodMk continuous_id))).sub continuous_const))
    have := hcont.tendsto g₀
    rwa [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem tendsto_rightRegular_of_continuous {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ rightRegular Γ μ g ((hc.memLp_of_hasCompactSupport hs).toLp ψ)) (𝓝 g₀)
      (𝓝 (rightRegular Γ μ g₀ ((hc.memLp_of_hasCompactSupport hs).toLp ψ))) := by
  have hψ : MemLp ψ 2 (quotientMeasure Γ μ) := hc.memLp_of_hasCompactSupport hs
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hae : ∀ g, ⇑(rightRegular Γ μ g (hψ.toLp ψ)) =ᵐ[quotientMeasure Γ μ]
      fun x ↦ ψ (rightMul Γ g x) := fun g ↦
    (coeFn_rightTranslate Γ μ g _).trans
      ((measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq_comp hψ.coeFn_toLp)
  have heq : ∀ g, eLpNorm (⇑(rightRegular Γ μ g (hψ.toLp ψ)) - ⇑(rightRegular Γ μ g₀ (hψ.toLp ψ)))
      2 (quotientMeasure Γ μ) = (∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
        ∂quotientMeasure Γ μ) ^ (1 / (2 : ℝ)) := fun g ↦ by
    rw [eLpNorm_congr_ae ((hae g).sub (hae g₀)),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  simp_rw [heq]
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
    (tendsto_lintegral_rightMul_sub Γ μ hc hs g₀)
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem continuous_rightRegular_apply (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    Continuous fun g ↦ rightRegular Γ μ g φ := by
  refine continuous_iff_continuousAt.2 fun g₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ψ, hs, hψφ, hc, hmem⟩ := (Lp.memLp φ).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 4)) (by simpa using hε4)
  set φ₀ : Lp ℂ 2 (quotientMeasure Γ μ) := (hc.memLp_of_hasCompactSupport hs).toLp ψ
  have hd : dist φ φ₀ ≤ ε / 4 := by
    rw [Lp.dist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp _))]
    exact ENNReal.toReal_le_of_le_ofReal hε4.le hψφ
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_rightRegular_of_continuous Γ μ hc hs g₀) (ε / 4)
    hε4] with g hg
  calc dist (rightRegular Γ μ g φ) (rightRegular Γ μ g₀ φ)
      ≤ dist (rightRegular Γ μ g φ) (rightRegular Γ μ g φ₀) +
          (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) +
            dist (rightRegular Γ μ g₀ φ₀) (rightRegular Γ μ g₀ φ)) :=
        (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ = dist φ φ₀ + (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) + dist φ₀ φ) := by
        rw [LinearIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map]
    _ < ε := by
        rw [dist_comm φ₀ φ]
        linarith

theorem continuous_rightRegular_prod :
    Continuous fun p : G × Lp ℂ 2 (quotientMeasure Γ μ) ↦ rightRegular Γ μ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨g₀, φ₀⟩ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have h1 := (continuous_rightRegular_apply Γ μ φ₀).tendsto g₀
  have h2 : ∀ᶠ p : G × Lp ℂ 2 (quotientMeasure Γ μ) in 𝓝 (g₀, φ₀),
      dist (rightRegular Γ μ p.1 φ₀) (rightRegular Γ μ g₀ φ₀) < ε / 2 :=
    (Metric.tendsto_nhds.1 h1 (ε / 2) (by positivity)).prod_inl_nhds φ₀
  have h3 : ∀ᶠ p : G × Lp ℂ 2 (quotientMeasure Γ μ) in 𝓝 (g₀, φ₀), dist p.2 φ₀ < ε / 2 :=
    (Metric.tendsto_nhds.1 tendsto_id (ε / 2) (by positivity)).prod_inr_nhds g₀
  filter_upwards [h2, h3] with p hp2 hp3
  calc dist (rightRegular Γ μ p.1 p.2) (rightRegular Γ μ g₀ φ₀)
      ≤ dist (rightRegular Γ μ p.1 p.2) (rightRegular Γ μ p.1 φ₀) +
          dist (rightRegular Γ μ p.1 φ₀) (rightRegular Γ μ g₀ φ₀) := dist_triangle _ _ _
    _ = dist p.2 φ₀ + dist (rightRegular Γ μ p.1 φ₀) (rightRegular Γ μ g₀ φ₀) := by
        rw [LinearIsometryEquiv.dist_map]
    _ < ε := by linarith

end Continuity

end RightCosetSpace

end

end GroundTheory.Automorphic
