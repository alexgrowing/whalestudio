import Mathlib
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem secondCountableTopology_subgroup_units (G : Subgroup 𝔸ˣ) : SecondCountableTopology G := by
  have hemb : Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  exact hemb.secondCountableTopology

noncomputable def BanachRep.integrated {K : Type*} [Group K] [TopologicalSpace K] [MeasurableSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep K E) (μ : Measure K)
    (f : K → ℂ) (v : E) : E :=
  ∫ g, f g • π g v ∂μ

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem continuous_iteratedFDeriv_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (ψ : P → G → E')
    (hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : P × 𝔤 => ψ q.1 (g₀ * h.expG q.2))) (k : ℕ) :
    Continuous (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨Y₀, g₀⟩
  set Φ : P × 𝔤 → E' := fun q => ψ q.1 (g₀ * h.expG q.2) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hψ g₀
  set L := ContinuousLinearMap.inl ℝ P 𝔤
  set H : P × 𝔤 → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : 𝔤) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × 𝔤 => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  letI := h.chartedSpace
  have hg₀ : g₀ ∈ (h.chart g₀).source := mem_chart_source 𝔤 g₀
  have hsrc : (h.chart g₀).source ∈ 𝓝 g₀ := (h.chart g₀).open_source.mem_nhds hg₀
  have hev : (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) =ᶠ[𝓝 (Y₀, g₀)]
      fun p => H (p.1, h.chart g₀ p.2) := by
    filter_upwards [prod_mem_nhds univ_mem hsrc] with p hp
    have e : (fun Y => ψ Y p.2) = fun Y => Φ (Y, h.chart g₀ p.2) := by
      funext Y
      simp only [hΦdef]
      rw [show g₀ * h.expG (h.chart g₀ p.2) = p.2 from (h.chart g₀).left_inv hp.2]
    rw [e, hpart]
  refine ContinuousAt.congr ?_ hev.symm
  exact hH.continuousAt.comp (continuousAt_fst.prodMk
    (((h.chart g₀).continuousAt hg₀).comp continuousAt_snd))

def IsTestFunction (f : G → ℂ) : Prop :=
  (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) ∧ HasCompactSupport f

theorem IsTestFunction.continuous {f : G → ℂ} (hf : h.IsTestFunction f) : Continuous f := by
  letI := h.chartedSpace
  exact hf.1.continuous

theorem contDiff_comp_expG_mul_expG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : G → F} (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ : V → 𝔤}
    (h₁ : ContDiff ℝ ∞ φ₁) (a : G) (h₂ : ContDiff ℝ ∞ φ₂) :
    ContDiff ℝ ∞ (fun p => f (h.expG (φ₁ p) * a * h.expG (φ₂ p))) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞ (fun p => h.expG (φ₁ p) * a * h.expG (φ₂ p)) :=
    ((h.contMDiff_expG_comp h₁).mul contMDiff_const).mul (h.contMDiff_expG_comp h₂)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem integrable_smul_orbit {f : G → ℂ} (hf : h.IsTestFunction f) (v : E) :
    Integrable (fun g => f g • π g v) μ := by
  haveI := secondCountableTopology_subgroup_units G
  refine ((hf.continuous h).smul (π.continuous_orbit v)).integrable_of_hasCompactSupport ?_
  exact hf.2.smul_right

theorem isSmoothVector_integrated {f : G → ℂ} (hf : h.IsTestFunction f) (v : E) :
    h.IsSmoothVector π (π.integrated μ f v) := by
  haveI := secondCountableTopology_subgroup_units G
  rw [isSmoothVector_iff]

  set F : 𝔤 → G → E := fun Y g => f (h.expG (-Y) * g) • π g v with hFdef
  have hexp : h.expOrbit π (π.integrated μ f v) = fun Y => ∫ g, F Y g ∂μ := by
    funext Y
    rw [expOrbit_apply, BanachRep.integrated,
      ← (π (h.expG Y)).integral_comp_comm (h.integrable_smul_orbit π μ hf v)]
    rw [← integral_mul_left_eq_self (F Y) (h.expG Y)]
    congr 1
    funext g
    simp only [hFdef, ContinuousLinearMap.coe_restrictScalars', map_smul,
      ← BanachRep.map_mul_apply, expG_neg, inv_mul_cancel_left]
  rw [hexp]

  set ψ : 𝔤 → G → ℂ := fun Y g => f (h.expG (-Y) * g) with hψdef
  have hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => ψ q.1 (g₀ * h.expG q.2)) := by
    intro g₀
    have := h.contDiff_comp_expG_mul_expG hf.1 (contDiff_fst.neg) g₀ contDiff_snd
    simpa [hψdef, mul_assoc] using this
  have hψY : ∀ g : G, ContDiff ℝ ∞ (fun Y => ψ Y g) := by
    intro g
    have := h.contDiff_comp_expG_mul_expG hf.1 (contDiff_id.neg) g (contDiff_const (c := (0 : 𝔤)))
    simpa [hψdef] using this

  set Lw : G → ℂ →L[ℝ] E := fun g => (ContinuousLinearMap.lsmul ℝ ℂ).flip (π g v) with hLw
  have hLwc : Continuous Lw := (ContinuousLinearMap.continuous _).comp (π.continuous_orbit v)
  have hFL : ∀ g, (fun Y => F Y g) = Lw g ∘ fun Y => ψ Y g := by
    intro g; funext Y; simp [hFdef, hLw, hψdef]
  have hiter : ∀ (k : ℕ) (Y : 𝔤) (g : G), ParamIntegral.iter F k Y g =
      (Lw g).compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun Y => ψ Y g) Y) := by
    intro k Y g
    rw [ParamIntegral.iter, hFL g]
    exact (Lw g).iteratedFDeriv_comp_left (hψY g).contDiffAt (by exact_mod_cast le_top)
  refine contDiff_integral_of_iteratedFDeriv F (fun g => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · rw [hFL g]; exact (Lw g).contDiff.comp (hψY g)
  · simp_rw [hiter]
    have hc := h.continuous_iteratedFDeriv_param ψ hψ k
    have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] E)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) E)
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ E)
    exact hB.comp ((hLwc.comp continuous_snd).prodMk hc)
  ·
    refine ⟨closedBall Y₀ 1, closedBall_mem_nhds Y₀ one_pos,
      (fun p : 𝔤 × G => h.expG p.1 * p.2) '' (closedBall Y₀ 1 ×ˢ tsupport f), ?_, ?_⟩
    · exact ((isCompact_closedBall Y₀ 1).prod hf.2).image
        ((h.continuous_expG.comp continuous_fst).mul continuous_snd)
    · intro Y hY g hg
      simp only [hFdef]
      by_contra hne
      apply hg
      refine ⟨(Y, h.expG (-Y) * g), ⟨hY, subset_tsupport f ?_⟩, ?_⟩
      · intro h0; apply hne; simp [h0]
      · simp [expG_neg]

omit [MeasurableSpace G] [BorelSpace G] in

theorem dense_smoothVectors : Dense (h.smoothVectors π : Set E) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI := h.locallyCompactSpace
  haveI := secondCountableTopology_subgroup_units G
  set μ : Measure G := Measure.haar
  rw [Metric.dense_iff]
  intro v r hr
  have hU : (fun g => π g v) ⁻¹' ball v (r / 2) ∈ 𝓝 (1 : G) :=
    (π.continuous_orbit v).continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds v (half_pos hr))
  letI := h.chartedSpace
  haveI := h.isManifold ∞
  obtain ⟨b, -, hbU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, 𝔤)) (1 : G)).mem_iff.1 hU
  set c : ℝ := ∫ g, b g ∂μ with hcdef
  have hc : 0 < c := b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    b.hasCompactSupport (fun x => b.nonneg) (x := 1) (by rw [b.eq_one]; exact one_ne_zero)
  set f : G → ℂ := fun g => ((c⁻¹ * b g : ℝ) : ℂ) with hfdef
  have hsupp : Function.support f ⊆ Function.support b := by
    intro g hg hb
    apply hg
    simp [hfdef, hb]
  have hf : h.IsTestFunction f := by
    refine ⟨?_, b.hasCompactSupport.mono hsupp⟩
    set L : ℝ →L[ℝ] ℂ := c⁻¹ • Complex.ofRealCLM
    have e : f = L ∘ b := by funext g; simp [L, hfdef]
    rw [e]
    exact L.contDiff.comp_contMDiff b.contMDiff
  have hfint : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hf.2
  have hint1 : ∫ g, f g ∂μ = 1 := by
    show ∫ g, ((c⁻¹ * b g : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne', Complex.ofReal_one]
  refine ⟨π.integrated μ f v, ?_, h.isSmoothVector_integrated π μ hf v⟩
  rw [mem_ball, dist_eq_norm]
  have e : π.integrated μ f v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub (h.integrable_smul_orbit π μ hf v) (hfint.smul_const v), integral_smul_const,
      hint1, one_smul]
    rfl
  rw [e]
  have hbound : ∀ g, ‖f g • (π g v - v)‖ ≤ (c⁻¹ * b g) * (r / 2) := by
    intro g
    rw [norm_smul, hfdef, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hc.le) b.nonneg)]
    by_cases hb : b g = 0
    · simp [hb]
    · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.2 hc.le) b.nonneg)
      have h2 := hbU (subset_tsupport _ hb)
      rw [mem_preimage, mem_ball, dist_eq_norm] at h2
      exact h2.le
  calc ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, (c⁻¹ * b g) * (r / 2) ∂μ :=
        norm_integral_le_of_norm_le ((b.continuous.integrable_of_hasCompactSupport
          b.hasCompactSupport).const_mul c⁻¹ |>.mul_const _) (Eventually.of_forall hbound)
    _ = r / 2 := by rw [integral_mul_const, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne', one_mul]
    _ < r := half_lt_self hr

end IsExpLieAlgebra

end GroundTheory.Automorphic
