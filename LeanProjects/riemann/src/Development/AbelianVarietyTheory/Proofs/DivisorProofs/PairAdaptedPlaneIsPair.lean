import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFunctionalVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneRestrictionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EvZeroKer

open scoped Classical in

theorem proj_adm {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) y) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (n₂ d₂ : ℕ) (X₂ : Spc F E n₂) (W₂ : Spc F E d₂) (M₂ : Model σ X₂ W₂) (ι : Matrix (Fin n) (Fin n₂) E) (ι' : Matrix (Fin d) (Fin d₂) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₂ d₂), M₂.IsGood B.ψ → iso0 n H' ⊆ I → IsEv B M M₂ ι ι' I e → ∀ Φ ∈ schA F (Fin n × Fin d), e₀ Φ = 0 → e Φ = 0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e₀ he₀
    n₂ d₂ X₂ W₂ M₂ ι ι' I e hM₂ hI he Φ hΦ h0
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨Y₀, S, hS, hSs, hSa, hSi, hSk⟩ := GlobalTheory.T.pair_adapted_plane_restriction F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e₀ he₀
  obtain ⟨φ, hφ, rfl⟩ := hSs Φ hΦ
  have hv := hSk φ hφ h0
  funext y
  have hl : (LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n₂ × Fin d₂ → AF F) => ℂ) y) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) :=
    GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n₂ d₂ X W X₂ W₂ M M₂ ι ι' I e hP.good hM₂ he _ (proj_adm _ y)
  obtain ⟨l', hl', hl'e⟩ := hSa _ hl
  have key := GlobalTheory.T.adelic_functional_vanishing F B.ψ hψ (Fin n × Fin d) Y₀ l' hl' (fun t y' hy' φ' hφ' => by
    obtain ⟨u, hu, hu'⟩ := hSi t y' hy'
    rw [hl'e _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ φ' hφ'), hl'e φ' hφ', hu' φ' hφ']
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [he.inv u (hI hu) _ (hS φ' hφ')]) φ hφ hv
  rw [hl'e φ hφ] at key
  simpa using key

end GlobalTheory.EvZeroKer
