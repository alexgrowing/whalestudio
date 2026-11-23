import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleFiniteMapsForallPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMatchedVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaL2DerivativeMatchedStatement

noncomputable section
namespace GlobalTheory.ThetaSkew
open MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem inner_toLp {f g : X → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hg.toLp g, hf.toLp f⟫_ℂ = ∫ x, f x * conj (g x) ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]

theorem tendsto_quot {f : ℝ → X → ℂ} {f₀ f₁ : X → ℂ} (hf : ∀ t, MemLp (f t) 2 ν) (hf₀ : MemLp f₀ 2 ν)
    (hf₁ : MemLp f₁ 2 ν)
    (df : Tendsto (fun t : ℝ => eLpNorm (fun x => (t : ℂ)⁻¹ * (f t x - f₀ x) - f₁ x) 2 ν) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • ((hf t).toLp (f t) - hf₀.toLp f₀)) (𝓝[≠] 0) (𝓝 (hf₁.toLp f₁)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ t : ℝ, ‖(t : ℂ)⁻¹ • ((hf t).toLp (f t) - hf₀.toLp f₀) - hf₁.toLp f₁‖ =
      (eLpNorm (fun x => (t : ℂ)⁻¹ * (f t x - f₀ x) - f₁ x) 2 ν).toReal := by
    intro t
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((t : ℂ)⁻¹ • ((hf t).toLp (f t) - hf₀.toLp f₀)) (hf₁.toLp f₁),
      Lp.coeFn_smul (t : ℂ)⁻¹ ((hf t).toLp (f t) - hf₀.toLp f₀),
      Lp.coeFn_sub ((hf t).toLp (f t)) (hf₀.toLp f₀), (hf t).coeFn_toLp, hf₀.coeFn_toLp, hf₁.coeFn_toLp]
      with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, h5, h6, smul_eq_mul]
  simp_rw [e]
  have h0 : (0 : ℝ) = (0 : ENNReal).toReal := rfl
  rw [h0]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp df

theorem sum_eq_zero_of_const {f g : ℝ → X → ℂ} {f₀ g₀ f₁ g₁ : X → ℂ}
    (hf : ∀ t, MemLp (f t) 2 ν) (hg : ∀ t, MemLp (g t) 2 ν) (hf₀ : MemLp f₀ 2 ν) (hg₀ : MemLp g₀ 2 ν)
    (hf₁ : MemLp f₁ 2 ν) (hg₁ : MemLp g₁ 2 ν)
    (df : Tendsto (fun t : ℝ => eLpNorm (fun x => (t : ℂ)⁻¹ * (f t x - f₀ x) - f₁ x) 2 ν) (𝓝[≠] 0) (𝓝 0))
    (dg : Tendsto (fun t : ℝ => eLpNorm (fun x => (t : ℂ)⁻¹ * (g t x - g₀ x) - g₁ x) 2 ν) (𝓝[≠] 0) (𝓝 0))
    (hc : ∀ t, ∫ x, f t x * conj (g t x) ∂ν = ∫ x, f₀ x * conj (g₀ x) ∂ν) :
    ∫ x, f₁ x * conj (g₀ x) ∂ν + ∫ x, f₀ x * conj (g₁ x) ∂ν = 0 := by
  set Ft := fun t => (hf t).toLp (f t)
  set Gt := fun t => (hg t).toLp (g t)
  set F₀ := hf₀.toLp f₀
  set G₀ := hg₀.toLp g₀
  set F₁ := hf₁.toLp f₁
  set G₁ := hg₁.toLp g₁
  have qf := tendsto_quot hf hf₀ hf₁ df
  have qg := tendsto_quot hg hg₀ hg₁ dg

  have hG : Tendsto Gt (𝓝[≠] 0) (𝓝 G₀) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) • ((t : ℂ)⁻¹ • (Gt t - G₀))) (𝓝[≠] 0) (𝓝 ((0 : ℂ) • G₁)) := by
      refine Tendsto.smul ?_ qg
      have : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => Gt t - G₀) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ht), one_smul]
    simpa using h2.add_const G₀

  have hid : ∀ t : ℝ, t ≠ 0 →
      ⟪Gt t, (t : ℂ)⁻¹ • (Ft t - F₀)⟫_ℂ + ⟪(t : ℂ)⁻¹ • (Gt t - G₀), F₀⟫_ℂ = 0 := by
    intro t _
    have e1 : ⟪Gt t, Ft t⟫_ℂ = ⟪G₀, F₀⟫_ℂ := by
      simp only [Gt, Ft, G₀, F₀, inner_toLp]; exact hc t
    rw [inner_smul_right, inner_smul_left, inner_sub_right, inner_sub_left, e1]
    have : (starRingEnd ℂ) ((t : ℂ)⁻¹) = (t : ℂ)⁻¹ := by simp
    rw [this]; ring
  have hlim : Tendsto (fun t : ℝ => ⟪Gt t, (t : ℂ)⁻¹ • (Ft t - F₀)⟫_ℂ + ⟪(t : ℂ)⁻¹ • (Gt t - G₀), F₀⟫_ℂ)
      (𝓝[≠] 0) (𝓝 (⟪G₀, F₁⟫_ℂ + ⟪G₁, F₀⟫_ℂ)) :=
    (hG.inner qf).add (qg.inner tendsto_const_nhds)
  have hz : Tendsto (fun t : ℝ => ⟪Gt t, (t : ℂ)⁻¹ • (Ft t - F₀)⟫_ℂ + ⟪(t : ℂ)⁻¹ • (Gt t - G₀), F₀⟫_ℂ)
      (𝓝[≠] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hid t ht).symm
  have := tendsto_nhds_unique hlim hz
  rw [inner_toLp hf₁ hg₀, inner_toLp hf₀ hg₁] at this
  exact this

end GlobalTheory.ThetaSkew

namespace GlobalTheory.ThetaSkew
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology

theorem skew : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → ∃ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧ (∫ x in 𝓕, G.M'.I om' Φ₁ x * starRingEnd ℂ (G.M'.I om' Ψ x) ∂μ) + ∫ x in 𝓕, G.M'.I om' Φ x * starRingEnd ℂ (G.M'.I om' Ψ₁ x) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 γ hγ Φ hΦ Ψ hΨ Ψ₁ hΨ₁ hdΨ
  obtain ⟨Φ₁, hΦ₁, hdΦ⟩ := GlobalTheory.T.matched_triple_finite_maps_forall_places hKP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ
  refine ⟨Φ₁, hΦ₁, hdΦ, ?_⟩
  have mem := GlobalTheory.T.theta_lift_matched_vanishing hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕
  have der := GlobalTheory.T.theta_l2_derivative_matched hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 γ hγ
  have mem0 : ∀ Θ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), MemLp (G.M'.I om' Θ) 2 (μ.restrict 𝓕) := by
    intro Θ hΘ
    have h1 := mem Θ hΘ 1
    simp only [mul_one] at h1
    exact h1
  exact sum_eq_zero_of_const (f := fun t x => G.M'.I om' Φ (x * γ (Multiplicative.ofAdd t)))
    (g := fun t x => G.M'.I om' Ψ (x * γ (Multiplicative.ofAdd t)))
    (fun t => mem Φ hΦ _) (fun t => mem Ψ hΨ _) (mem0 Φ hΦ) (mem0 Ψ hΨ) (mem0 Φ₁ hΦ₁) (mem0 Ψ₁ hΨ₁)
    (der Φ hΦ Φ₁ hΦ₁ hdΦ) (der Ψ hΨ Ψ₁ hΨ₁ hdΨ)
    (fun t => GlobalTheory.T.matched_pair_theta_finite_places hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ Ψ hΨ _)

end GlobalTheory.ThetaSkew
