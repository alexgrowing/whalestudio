import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicInvariantSplitPlacesConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaIntegralRationalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteAdaptedPlaneThetaReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteAdaptedPlaneThetaIdentity

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

namespace GlobalTheory.ThK.LiftConst

theorem thetaLiftAnisotropic_const : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → fa = c • fa' ∧ fb = c • fb') →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ Φ₁, ∀ Φ₁' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ₁ Φ₁' →
      ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
        ∀ g g' : UA σ G.V'.J, ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om' Φ₁' g h) ∂μ =
          ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (theta om' Φ₁' g' h) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hc Φ Φ' hΦ' hPM hCT hdec Φ₁ Φ₁' hΦ₁' hPM₁
    μ 𝓕 hμ h𝓕 g g'
  obtain ⟨T, hT⟩ := GlobalTheory.T.definite_adapted_plane_theta_identity hKP F E σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hc Φ Φ' hΦ' hPM hCT hdec Φ₁ Φ₁'
    hΦ₁' hPM₁ μ 𝓕 hμ h𝓕
  exact GlobalTheory.T.automorphic_invariant_split_places_const hKP F E σ B a' G.V' G.q (a' - G.q) hM.triple.base hM.triple.geo.hV' T _
    (GlobalTheory.T.definite_adapted_plane_theta_reduction hKP F E σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hc Φ Φ' hΦ' hPM hCT hdec Φ₁ Φ₁' hΦ₁' hPM₁
      μ 𝓕 hμ h𝓕)
    (GlobalTheory.T.matched_theta_integral_rational_invariant hKP F E σ B a a' G X om om' R Rf hM Φ₁' hΦ₁' μ 𝓕 _) hT g g'

end GlobalTheory.ThK.LiftConst
