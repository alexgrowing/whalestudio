import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentSmoothStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKAdm

theorem admissible : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Φ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ P : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ[ℂ] ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), P Φ = Φ ∧ (∀ Ψ, P (P Ψ) = P Ψ) ∧ (∀ Ψ Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∫ x in 𝓕, G.M'.I om' ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x * starRingEnd ℂ (G.M'.I om' ((Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x) ∂μ = ∫ x in 𝓕, G.M'.I om' ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x * starRingEnd ℂ (G.M'.I om' ((P Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x) ∂μ) ∧ (∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a' (a + a')), GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → N ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) → ∀ Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) ∈ N → ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) ∈ N) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) => G.M'.I om' ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')))) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ
  obtain ⟨L, hL, PL, hPLΦ, hPLidem, hPLsa, hPLN, hPLfix, hPLk⟩ := GlobalTheory.T.matched_theta_descent_nonvanishing hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ
  obtain ⟨m, τ, hτ, Pξ, hPξΦ, hPξidem, hPξsa, hPξN, hPξty, hPξfix, hPξcomm⟩ :=
    GlobalTheory.T.matched_theta_descent_regular hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ
  have hc : ∀ Ψ, Pξ (PL Ψ) = PL (Pξ Ψ) := hPξcomm PL hPLk
  refine ⟨Pξ ∘ₗ PL, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.comp_apply, hPLΦ, hPξΦ]
  · intro Ψ
    simp only [LinearMap.comp_apply]
    rw [← hc (PL Ψ), hPξidem, hPLidem]
  · intro Ψ Ψ'
    simp only [LinearMap.comp_apply]
    rw [hPξsa, hPLsa, ← hc Ψ']
  · intro N hN hND Ψ hΨ
    exact hPξN N hN hND _ (hPLN N hN hND Ψ hΨ)
  · have hfin := GlobalTheory.T.matched_theta_descent_smooth hKP F E σ B a a' G X om om' R Rf hM L hL m τ hτ
    have hsub : Set.range (fun Ψ : ↥(PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) => G.M'.I om' (((Pξ ∘ₗ PL) Ψ : ↥(PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : Fn F a' (a + a'))) ⊆
        G.M'.I om' '' {Ψ | Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ (∀ l ∈ L, om' (1, l) Ψ = Ψ) ∧ GlobalTheory.ThKAdm.HasTypes B om' τ Ψ} := by
      rintro _ ⟨Ψ, rfl⟩
      exact ⟨_, ⟨(Pξ (PL Ψ)).2, fun l hl => hPξfix l (hL.1 hl) (PL Ψ) (hPLfix Ψ l hl), hPξty (PL Ψ)⟩, rfl⟩
    haveI := hfin
    exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end GlobalTheory.ThKAdm
