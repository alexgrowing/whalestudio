import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeStabP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairEigenUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizerStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.UnipEv

theorem unip_evalZero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu Φ hΦ
  have hS := hP.weil.isUSplitting
  have pres : ∀ g, ∀ φ ∈ schA F (Fin n × Fin d), om g φ ∈ schA F (Fin n × Fin d) := fun g φ hφ => hS.pres g φ hφ
  have key : ∀ g ∈ stabilizer₂ σ W H', ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, g) Φ) = c • e Φ := by
    intro g hg
    refine GlobalTheory.T.skew_adapted_pair_constant_term hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he
      (e ∘ₗ om (1, g)) ?_ ?_ ?_
    · exact GlobalTheory.T.skew_adapted_pair_eigen_unique F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he g hg
    · exact GlobalTheory.T.skew_adapted_pair_vanishing F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he g hg
    · intro y
      have h1 := GlobalTheory.T.skew_adapted_pair_seesaw F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he y
      have h2 := hS.adm (1, g) _ h1
      rwa [LinearMap.comp_assoc] at h2
  choose! c hc using key
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.skew_adapted_pair_integral F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he
  have inj : Function.Injective fun a : ℂ => a • e Φ₀ := smul_left_injective ℂ hne
  have hmul : ∀ g ∈ stabilizer₂ σ W H', ∀ h ∈ stabilizer₂ σ W H', c (g * h) = c g * c h := by
    intro g hg h hh
    apply inj
    have e1 : om (1, g * h) = om (1, g) * om (1, h) := by
      rw [← map_mul]; congr 1; ext <;> simp
    show c (g * h) • e Φ₀ = (c g * c h) • e Φ₀
    rw [← hc _ (mul_mem hg hh) Φ₀ hΦ₀, e1, Module.End.mul_apply, hc g hg _ (pres _ _ hΦ₀), hc h hh Φ₀ hΦ₀, smul_smul]
  have hone : c 1 = 1 := by
    apply inj
    show c 1 • e Φ₀ = (1 : ℂ) • e Φ₀
    rw [← hc 1 (one_mem _) Φ₀ hΦ₀, one_smul]
    have : ((1, 1) : UA σ X.J × UA σ W.J) = 1 := rfl
    rw [this, map_one, Module.End.one_apply]
  have hcu := GlobalTheory.T.character_multiplicative_stabilizer F E σ B d W d₁ W₁ H' i₀ i₁ r' s' r₁ s₁ hP.base hP.skew hP₁.skew hH c hmul hone u hu
  rw [hc u (unip_le_stabP W H' hu) Φ hΦ, hcu, one_smul]

end GlobalTheory.UnipEv
