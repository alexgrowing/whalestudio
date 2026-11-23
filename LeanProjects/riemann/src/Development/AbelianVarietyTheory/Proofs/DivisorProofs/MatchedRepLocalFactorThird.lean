import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKTypes

theorem types_transport : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), GlobalTheory.ThKAdm.IsLevel G.W L → ∀ (m : ℕ) (τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))), GlobalTheory.ThKAdm.IsKRep B τ → ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (e : I.GA →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), 1 ≤ g → GlobalTheory.ThKAdm.IsTransp B G.W L I g e → GlobalTheory.Dec.IsURep (fun k : GlobalTheory.Dec.Kinf I => τ (e (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1))) ∧ ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), GlobalTheory.ThKAdm.HasTypes B om' τ Ψ → ∃ T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (I.GA → ℂ), (∀ (k : GlobalTheory.Dec.Kinf I) w x, T (τ (e (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1)) w) x = T w (x * (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1))) ∧ (fun y => G.M'.I om' Ψ (e y)) ∈ LinearMap.range T := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM L hL m τ hτ I g e hg he
  obtain ⟨h1, hmul, hiso, hcont⟩ := hτ
  let ι : GlobalTheory.Dec.Kinf I → I.GA := fun k => (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1)
  have hι1 : ι 1 = 1 := rfl
  have hιmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => Prod.ext rfl (mul_one 1).symm
  have hιc : Continuous ι :=
    Continuous.prodMk (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v)) continuous_const
  have hk : ∀ k, e (ι k) ∈ KInf σ G.W B.emb := he.kinf
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show τ (e (ι 1)) = 1
    rw [hι1, map_one, h1]
  · intro x y
    show τ (e (ι (x * y))) = τ (e (ι x)) ∘SL τ (e (ι y))
    rw [hιmul, map_mul, hmul _ (hk x) _ (hk y)]
    rfl
  · intro k v
    exact hiso _ (hk k) v
  · intro v
    exact (hcont v).comp_continuous (he.cont.comp hιc) hk
  · rintro Ψ hΨ ⟨T₀, hT₀, v₀, hv₀⟩
    have hD := (GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).2
    have hlin := GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM
    let S : Submodule ℂ (EuclideanSpace ℂ (Fin m)) := (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁).comap T₀
    have hS : ∀ k ∈ KInf σ G.W B.emb, ∀ w ∈ S, τ k w ∈ S := by
      intro k hk w hw
      rw [Submodule.mem_comap] at hw ⊢
      rw [hT₀ k hk]
      exact hD k hk _ hw
    have hinner : ∀ k ∈ KInf σ G.W B.emb, ∀ x y, inner ℂ (τ k x) (τ k y) = inner ℂ x y := by
      intro k hk x y
      let li : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
        { toLinearMap := (τ k).toLinearMap, norm_map' := hiso k hk }
      exact li.inner_map_map x y
    have hcomm : ∀ k ∈ KInf σ G.W B.emb, ∀ w,
        S.starProjection (τ k w) = τ k (S.starProjection w) := by
      intro k hk w
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · exact hS k hk _ (S.starProjection_apply_mem w)
      · intro s hs
        have hk' := GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb hk
        have hs' : s = τ k (τ k⁻¹ s) := by
          rw [← ContinuousLinearMap.mul_apply, ← hmul _ hk _ hk', mul_inv_cancel, h1]
          rfl
        rw [hs', ← map_sub, hinner k hk]
        exact Submodule.starProjection_inner_eq_zero w _ (hS _ hk' s hs)
    let T₁ := T₀.comp (S.starProjection : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)).toLinearMap
    have hT₁D : ∀ w, T₁ w ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun w => S.starProjection_apply_mem w
    have hT₁ : ∀ k ∈ KInf σ G.W B.emb, ∀ w, T₁ (τ k w) = om' (1, k) (T₁ w) := by
      intro k hk w
      show T₀ (S.starProjection (τ k w)) = _
      rw [hcomm k hk w, hT₀ k hk]
      rfl
    have hI0 : G.M'.I om' 0 = 0 := by
      have h := hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
      rw [smul_zero, add_zero, one_smul] at h
      exact (left_eq_add.mp h)
    let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (I.GA → ℂ) :=
      { toFun := fun w y => G.M'.I om' (T₁ w) (e y)
        map_add' := fun w w' => by
          funext y
          have h := hlin _ (hT₁D w) _ (hT₁D w') 1
          simp only [one_smul] at h
          show G.M'.I om' (T₁ (w + w')) (e y) = G.M'.I om' (T₁ w) (e y) + G.M'.I om' (T₁ w') (e y)
          rw [map_add, h]
          rfl
        map_smul' := fun c w => by
          funext y
          have h := hlin 0 (Submodule.zero_mem _) _ (hT₁D w) c
          rw [zero_add, hI0, zero_add] at h
          show G.M'.I om' (T₁ (c • w)) (e y) = c • G.M'.I om' (T₁ w) (e y)
          rw [map_smul, h]
          rfl }
    refine ⟨T, ?_, v₀, ?_⟩
    · intro k w x
      show G.M'.I om' (T₁ (τ (e (ι k)) w)) (e x) = G.M'.I om' (T₁ w) (e (x * ι k))
      rw [hT₁ _ (hk k), GlobalTheory.ThetaFacCompl.I_transl, map_mul]
    · have hv : v₀ ∈ S := by
        rw [Submodule.mem_comap, hv₀]
        exact hΨ
      funext y
      show G.M'.I om' (T₀ (S.starProjection v₀)) (e y) = _
      rw [(Submodule.starProjection_eq_self_iff).2 hv, hv₀]

end GlobalTheory.ThKTypes

end
