import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedAdaptedPlaneScalarIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_adapted_plane_scalar_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
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
        ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
          V₁.J = H.ιᵀ * G.V.J * H.ι.map σ → M₁.IsGood B.ψ →
          IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e → ∃ C₀ : ℂ,
          IsCT (W := G.V) H (fun g : UA σ G.V.J => ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om Φ₁ g h) ∂μ)
            (fun g => C₀ * ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Φ₁))) ∂μ) := by
  first | exact @GlobalTheory.ThKTowerCT.constTerm_lift | exact GlobalTheory.ThKTowerCT.constTerm_lift | (intros; apply GlobalTheory.ThKTowerCT.constTerm_lift <;> assumption)
