import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicPairEisensteinExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormYXNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CtConvZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnNormMulQhtPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHeightBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinUnfoldingRapidDecayStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKDblCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCT_mul {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) {T : UA σ W.J → ℂ} (κ : ℂ)
    (h : IsCT H' T 0) : IsCT H' (fun x => κ * T x) 0 := by
  intro μ 𝓕 hμ h𝓕 h1 x
  have e := h μ 𝓕 hμ h𝓕 h1 x
  simp only [Pi.zero_apply] at e ⊢
  rw [integral_const_mul, ← e, mul_zero]

theorem isPair_larger {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) := by
  refine ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ,
    ⟨h.chars.heckeβ.1.div' h.chars.heckeα.1, fun x => by
      simp only [MonoidHom.div_apply, h.chars.heckeβ.2 x, h.chars.heckeα.2 x, div_self']⟩,
    h.chars.resβ, fun x => ?_, h.weil⟩
  have e := h.chars.resβ x
  have e' := h.chars.resα x
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ a' with hm | hm <;> rw [hm] <;> ring

theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

end GlobalTheory.ThKDblCore

theorem GlobalTheory.ThKDblCore.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∀ Φ₁ ∈ PolData B G.M, ∀ Φ₂ ∈ PolData B G.M,
    ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
    ∀ f : UA σ G.W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h) →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → GlobalTheory.ThKLiftCusp.IsCuspW G.W f →
      IsCT H' (fun x => ∫ h' in 𝓕, f h' * GlobalTheory.ThKLiftCusp.kern G.M om Φ₂ Φ₁ x h' ∂μ) 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hp d₁ W₁ H' i₀ i₁ hA Φ₁ hΦ₁ Φ₂ hΦ₂ μ 𝓕 hμ h𝓕 f hfc hfl hfd hcusp
  have hlt := hM.triple.geo.lt
  obtain ⟨Ez, φ, s₀, κ, R₀, -, hK, hreg, hunf⟩ :=
    GlobalTheory.T.anisotropic_pair_eisenstein_exists hKP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThKDblCore.isPair_larger hM.triple)
      (by rw [hp]; exact Nat.min_zero _) (by omega) (by omega) Φ₂ hΦ₂ Φ₁ hΦ₁ μ hμ
  have hct : IsCT H' f 0 := GlobalTheory.ThKLineCusp.const_term_zero F E σ B G.W _ _ hM.triple.geo.hW W₁ H' i₀ i₁ hA f hcusp
  have hbd : ∃ C : ℝ, ∀ h, ‖f h‖ ≤ C := by
    obtain ⟨C, hC⟩ := hfd 0
    exact ⟨C, fun h => by simpa using hC h⟩
  have hint := GlobalTheory.RapidInteg.integrableOn_norm_mul_qht_pow hKP F E σ B G.W _ _ hM.triple.base hM.triple.geo.hW
    μ 𝓕 hμ h𝓕 f hfc hfd
  have hN := GlobalTheory.T.unipotent_height_bounded F E σ (GlobalTheory.ThKDblCore.sigma_sigma hM.triple.base.cm) B G.W _ _ hM.triple.geo.hW W₁ H' i₀ i₁ hA
  have hhalf : ∀ s : ℂ, R₀ < s.re → IsCT H' (fun h => ∫ h' in 𝓕, f h' * Ez s h h' ∂μ) 0 := by
    intro s hs
    obtain ⟨hφ, hu⟩ := hunf s hs
    have e : (fun h => ∫ h' in 𝓕, f h' * Ez s h h' ∂μ) = fun h => ∫ g, φ s g * f (h * g) ∂μ :=
      funext (hu 𝓕 h𝓕 f hfc hfl hfd hcusp)
    rw [e]
    exact GlobalTheory.ConvCT.ct_conv_zero F E σ G.W H' μ hμ f (φ s) hfc hbd hφ hct
  have h0 := GlobalTheory.T.eisenstein_unfolding_rapid_decay F E σ G.W H' μ hμ 𝓕 f Ez s₀ R₀ hfc hint hN hreg hhalf
  have e2 : (fun x => ∫ h' in 𝓕, f h' * GlobalTheory.ThKLiftCusp.kern G.M om Φ₂ Φ₁ x h' ∂μ) =
      fun x => κ * ∫ h' in 𝓕, f h' * Ez s₀ x h' ∂μ := by
    funext x
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h' => ?_)
    simp only [hK]
    ring
  rw [e2]
  exact GlobalTheory.ThKDblCore.isCT_mul H' κ h0
