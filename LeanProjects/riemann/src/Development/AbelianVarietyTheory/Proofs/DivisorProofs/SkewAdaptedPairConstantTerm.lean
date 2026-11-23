import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesEvalZeroFormMemAdmissible
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeStabP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.UnipUniq

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ T : Fn F n d →ₗ[ℂ] Fn F n d₁,
        (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (T Φ)) →
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ u Φ) = T Φ) →
        (∀ y, (LinearMap.proj y : Fn F n d₁ →ₗ[ℂ] ℂ).comp T ∈ (adeleClass F).adm (Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), T Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he T hTh hTi hTa
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
  have hadmT : GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d) := hTa 0
  have hadmE : GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) :=
    GlobalTheory.T.eigen_intertwiner_composition F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ (GlobalTheory.MixUniq.adelicCoordinatesEvalZeroForm_mem_admissible _)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hψ (Fin n × Fin d) L hiso hrk _ hadmT _ hadmE
    (fun t w hw Φ hΦ => GlobalTheory.MixUniq.evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' T hTh hTi _ (hL t w hw) Φ hΦ)
    (fun t w hw Φ hΦ => GlobalTheory.MixUniq.evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' e he.Heisenberg₂ he.inv _ (hL t w hw) Φ hΦ)
    ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ₀ hΦ₀, by
      rw [LinearMap.comp_apply, ← GlobalTheory.MixUniq.apply_eq_evaluation_zero M M₁ B.ψ H'.ι e he.Heisenberg₂ Φ₀ hΦ₀ y]; exact hy⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [GlobalTheory.MixUniq.apply_eq_evaluation_zero M M₁ B.ψ H'.ι T hTh Φ hΦ y, Pi.smul_apply,
    GlobalTheory.MixUniq.apply_eq_evaluation_zero M M₁ B.ψ H'.ι e he.Heisenberg₂ Φ hΦ y, smul_eq_mul]
  exact hc _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ)

end GlobalTheory.UnipUniq
