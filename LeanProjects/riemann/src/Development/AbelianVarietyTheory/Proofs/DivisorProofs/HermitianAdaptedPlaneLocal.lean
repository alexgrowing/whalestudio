import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionIsPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXUniq

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he e' hheis hinv hpt
  have hstd : IsStd B.ψ := hP.base.std
  let δ : Fn F n₁ d →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n₁ × Fin d) := GlobalTheory.EvZeroUniq.proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.EvZeroUniq.schr_mem_schA _ hstd _ hΦ
  have hδe : ∀ (f : Fn F n₁ d) x, f x = δ (M₁.co.rho B.ψ (M₁.co.e.symm (x, 0)) f) := fun f x =>
    GlobalTheory.EvZeroUniq.apply_eq_rho _ _ f x
  have hfix : ∀ z, (M₁.co.e z).1 = 0 → ∀ f : Fn F n₁ d, δ (M₁.co.rho B.ψ z f) = δ f :=
    fun z hz f => GlobalTheory.EvZeroUniq.rho_apply_zero _ _ f z hz
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_extension F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hP₁.good he
  obtain ⟨x₀, hx₀⟩ : ∃ x, e Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨L, hLiso, hLrank, hL⟩ := GlobalTheory.T.adapted_plane_restriction_is_pair F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  have hinvL : ∀ l : Fn F n d →ₗ[ℂ] ℂ, (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
      ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ) →
      (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = l Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d),
        l (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ := by
    intro l h1 h2 t w hw φ hφ
    obtain ⟨u, hu, z, hz, heq⟩ := hL t w hw
    rw [heq φ, h1 u hu _ (hρ _ φ hφ), h2 z hz φ hφ]
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d) L hLiso hLrank (δ ∘ₗ e') (hpt 0) (δ ∘ₗ e)
    (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hP₁.good he δ hδ)
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hinv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hheis z Φ hΦ, hfix z hz]))
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]))
    ⟨_, hρ (incM F H.ι * M₁.co.e.symm (x₀, 0) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [he.Heisenberg₂ _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F H.ι * M₁.co.e.symm (x, 0) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

end GlobalTheory.MixXUniq
