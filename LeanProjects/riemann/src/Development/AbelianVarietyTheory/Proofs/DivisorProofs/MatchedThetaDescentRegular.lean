import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLevelSubgroupClosedMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteVectorsFiniteMatrixCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalEquivarianceStatement

namespace GlobalTheory.ThKTypes

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem exists_typeProj : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field
    E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B
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
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ
  have hstab := (GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).2
  obtain ⟨h1, hmul, hcomm⟩ := GlobalTheory.T.archimedean_level_subgroup_closed_mul F E σ (a + a') G.W B.emb
  have hinv : ∀ k ∈ KInf σ G.W B.emb, k⁻¹ ∈ KInf σ G.W B.emb := fun k hk => GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb hk
  let ρ : UA σ G.W.J →* Module.End ℂ (Fn F a' (a + a')) := om'.comp (MonoidHom.inr _ _)
  obtain ⟨m, τ, hτ, P, hPΦ, hPP, hjoint, htypes⟩ := GlobalTheory.T.K_finite_vectors_finite_matrix_coeff (UA σ G.W.J) (KInf σ G.W B.emb) (Fn F a' (a + a')) ρ
    (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) h1 hmul hinv hstab (GlobalTheory.T.matched_triple_local_invariance hKP F E σ B a a' G X om om' R Rf hM) Φ
  refine ⟨m, τ, hτ, P, hPΦ, hPP, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ψ Ψ'
    obtain ⟨n, c, k, hk, hx, -, hy⟩ := hjoint Ψ Ψ'
    rw [hx, hy]
    exact GlobalTheory.T.matched_triple_local_equivariance hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 _ Ψ.2 _ Ψ'.2 n c k hk
  · intro N hN _ Ψ hΨ
    obtain ⟨n, c, k, hk, hx, -, -⟩ := hjoint Ψ Ψ
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => N.smul_mem _ (hN.cpt _ (hk i) _ hΨ)
  · intro Ψ
    obtain ⟨T, hT, hr⟩ := htypes Ψ
    exact ⟨T, hT, hr⟩
  · intro l hl Ψ hfix
    obtain ⟨n, c, k, hk, hx, -, -⟩ := hjoint Ψ Ψ
    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    show om' (1, l) (om' (1, k i) (Ψ : Fn F a' (a + a'))) = om' (1, k i) (Ψ : Fn F a' (a + a'))
    have e : om' (1, l) (om' (1, k i) (Ψ : Fn F a' (a + a'))) = om' (1, k i) (om' (1, l) (Ψ : Fn F a' (a + a'))) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        hcomm l hl (k i) (hk i)]
    rw [e, hfix]
  · intro T hT Ψ
    obtain ⟨n, c, k, hk, hx, hy, -⟩ := hjoint Ψ (T Ψ)
    have hPΨ : P Ψ = ∑ i, c i • (⟨om' (1, k i) (Ψ : Fn F a' (a + a')), hstab _ (hk i) _ Ψ.2⟩ : ↥(PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) := by
      apply Subtype.ext
      rw [hx, Submodule.coe_sum]
      rfl
    apply Subtype.ext
    rw [hy, hPΨ, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul]
    congr 1
    exact (hT (k i) (hk i) Ψ _ rfl).symm

end GlobalTheory.ThKTypes
