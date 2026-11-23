import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentRegular
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_theta_descent_regular : GlobalTheory.ThK.KP → ∀ (F E
    : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om'
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ
    : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ
    G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ
    G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU
    σ G.W.J) 𝓕 μ → ∀ Φ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ (m : ℕ) (τ
    : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J → (EuclideanSpace ℂ (Fin
    m) →L[ℂ] EuclideanSpace ℂ (Fin
    m))), GlobalTheory.ThKAdm.IsKRep B τ ∧ ∃ P : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁) →ₗ[ℂ] ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), P Φ = Φ ∧ (∀ Ψ, P (P
    Ψ) = P Ψ) ∧ (∀ Ψ Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁), ∫ x in 𝓕, G.M'.I om' ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))
    : GlobalTheory.ThK.Fn F a' (a + a')) x * starRingEnd ℂ (G.M'.I om' ((Ψ'
    : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a'))
    x) ∂μ = ∫ x in 𝓕, G.M'.I om' ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))
    : GlobalTheory.ThK.Fn F a' (a + a')) x * starRingEnd ℂ (G.M'.I om' ((P Ψ'
    : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a'))
    x) ∂μ) ∧ (∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a' (a +
    a')), GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁) N → N ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁) → ∀ Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ((Ψ
    : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a +
    a')) ∈ N → ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))
    : GlobalTheory.ThK.Fn F a' (a + a')) ∈ N) ∧ (∀ Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So
    B.ψ B.τ₁), GlobalTheory.ThKAdm.HasTypes B om' τ ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓
    G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a +
    a'))) ∧ (∀ l ∈ GlobalTheory.ThKAdm.FinPt σ G.W, ∀ Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓
    G.M'.So B.ψ B.τ₁), om' (1, l) ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))
    : GlobalTheory.ThK.Fn F a' (a + a')) = ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) → om' (1, l) ((P Ψ : ↥(GlobalTheory.ThK.PolData B
    G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) = ((P Ψ
    : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a +
    a'))) ∧ (∀ T : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁) →ₗ[ℂ] ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ
    B.τ₁), (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ Ψ Ψ' : ↥(GlobalTheory.ThK.PolData
    B G.M' ⊓ G.M'.So B.ψ B.τ₁), ((Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))
    : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓
    G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) → ((T Ψ' : ↥(GlobalTheory.ThK.PolData B
    G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) ((T Ψ
    : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a +
    a'))) → ∀ Ψ, P (T Ψ) = T (P Ψ)) := by
  first | exact @GlobalTheory.ThKTypes.exists_typeProj | exact GlobalTheory.ThKTypes.exists_typeProj | (intros; apply GlobalTheory.ThKTypes.exists_typeProj <;> assumption)
