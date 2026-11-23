import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationHaarUnfoldingSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasureStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.IwasawaUnfold

theorem iwasawa_unfold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ f : UA σ G.V.J → ℂ, Continuous f →
      (∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}, ∀ g, f (q * g) = f g) →
      (∀ n ∈ unip σ G.V H, ∀ g, f (n * g) = f g) →
      ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ‖f (m l g₀ * k.1)‖ₑ * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK < ⊤ →
      ∫ g in 𝓓, f g ∂G.M.μ = C * ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, f (m l g₀ * k.1) * (((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) ∂G₁.M.μ ∂μ ∂μK := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ K μK μ hK hμK hμ m hm
  obtain ⟨μN, c, hμN, hc0, hctop, hI⟩ := GlobalTheory.T.doubling_configuration_haar_unfolding_second F E σ B b a' G G₁ H H' hC hB hG hG₁ K μK μ hK hμK hμ m hm
  obtain ⟨C, hC0, hCtop, hU⟩ := GlobalTheory.T.config_a_haar_unfolding F E σ B b a' G G₁ H H' hC hB hG hG₁ K μK μ hK hμK hμ m hm μN c hμN hc0 hctop hI
  refine ⟨(C.toReal : ℂ), ?_, ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos hC0 hCtop).ne'
  intro 𝓓 h𝓓 f hf hQ hN hfin
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have key : ∀ p : ℂ → ENNReal, Continuous p → ∫⁻ g in 𝓓, p (f g) ∂G.M.μ =
      C * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, p (f (m l g₀ * k.1)) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK :=
    fun p hp => hU 𝓓 h𝓓 (fun g => p (f g)) (hp.comp hf) (fun q hq g => by simp only [hQ q hq g])
      (fun n hn g => by simp only [hN n hn g])
  have hint : IntegrableOn f 𝓓 G.M.μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖f a‖ₑ ∂(G.M.μ.restrict 𝓓) < ⊤
    rw [key (fun z => ‖z‖ₑ) continuous_enorm]
    exact ENNReal.mul_lt_top hCtop.lt_top hfin
  have hre := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (μ := G.M.μ.restrict 𝓓) (f := fun g => (f g).re) hint.re
  have him := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (μ := G.M.μ.restrict 𝓓) (f := fun g => (f g).im) hint.im
  rw [key (fun z => ENNReal.ofReal z.re) (ENNReal.continuous_ofReal.comp Complex.continuous_re),
    key (fun z => ENNReal.ofReal (-z.re)) (ENNReal.continuous_ofReal.comp Complex.continuous_re.neg)] at hre
  rw [key (fun z => ENNReal.ofReal z.im) (ENNReal.continuous_ofReal.comp Complex.continuous_im),
    key (fun z => ENNReal.ofReal (-z.im)) (ENNReal.continuous_ofReal.comp Complex.continuous_im.neg)] at him
  rw [GlobalTheory.T.config_a_haar_unfolding_measure F E σ B b a' G G₁ H H' hC hB hG hG₁ K μK μ hK hμK hμ m hm f hf hfin]
  apply Complex.ext
  · have e1 : (∫ g in 𝓓, f g ∂G.M.μ).re = ∫ g in 𝓓, (f g).re ∂G.M.μ := (integral_re hint).symm
    rw [e1]
    simp only [ENNReal.toReal_mul] at hre
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.add_im, Complex.I_re, Complex.I_im]
    rw [hre]; ring
  · have e1 : (∫ g in 𝓓, f g ∂G.M.μ).im = ∫ g in 𝓓, (f g).im ∂G.M.μ := (integral_im hint).symm
    rw [e1]
    simp only [ENNReal.toReal_mul] at him
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.add_im, Complex.I_re, Complex.I_im]
    rw [him]; ring
end GlobalTheory.IwasawaUnfold
