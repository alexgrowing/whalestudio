import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleHyperbolicPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedAdaptedPlaneScalarIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedAdaptedPlaneScalarRelationStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKOrthACusp

theorem cusp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      ∀ Φ ∈ PolData B G.M, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ Φ₁ ∈ PolData B G.M,
      ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
      ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
        IsCT (W := G.V) H (fun g : UA σ G.V.J => ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om Φ₁ g h) ∂μ) 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM d₁ W₁ H' i₀ i₁ hH' c Φ hΦ Φ' hΦ' hct hdec Φ₁ hΦ₁ μ 𝓕 hμ h𝓕 d₂ H hH
  obtain ⟨V₁, M₁, e, hJ, hM₁, he⟩ := GlobalTheory.T.triple_hyperbolic_plane_split hKP F E σ B a a' G X om om' hM.triple d₂ H hH
  obtain ⟨C₀, hCT⟩ := GlobalTheory.T.matched_adapted_plane_scalar_identity hKP F E σ B a a' G X om om' R Rf hM d₁ W₁ H' i₀ i₁ hH' c Φ hΦ Φ' hΦ' hct hdec Φ₁ hΦ₁ μ 𝓕 hμ h𝓕 d₂ H hH V₁ M₁ e hJ hM₁ he
  have h0 := GlobalTheory.T.matched_adapted_plane_scalar_relation hKP F E σ B a a' G X om om' R Rf hM d₁ W₁ H' i₀ i₁ hH' c Φ hΦ Φ' hΦ' hct hdec Φ₁ hΦ₁ μ 𝓕 hμ h𝓕 d₂ H hH V₁ M₁ e hJ hM₁ he
  intro ν 𝓖 hν h𝓖 hmass g
  rw [← hCT ν 𝓖 hν h𝓖 hmass g]
  simp only [Pi.zero_apply, h0 g, mul_zero]

end GlobalTheory.ThKOrthACusp
