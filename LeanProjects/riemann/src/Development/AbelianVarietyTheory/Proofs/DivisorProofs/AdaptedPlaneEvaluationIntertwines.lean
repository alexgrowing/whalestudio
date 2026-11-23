import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKSwapCont

theorem continuous_term : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Ψ ∈ schA F (Fin n × Fin d),
      ∀ ξ : Fin n → E, Continuous (fun u : unip σ W H' => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))) := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ _ hM₁ e₀ hE χX χW om r s r' s' hP Ψ hΨ ξ
  have hM := hP.good
  have hψ := hP.base.std
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d₁)
  set w := M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))
  have hl := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ w (GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE hl₀)
  have hc := hP.weil.2.2 _ hl Ψ hΨ
  have hsplit := hP.weil.isUSplitting
  have heq : (fun u : unip σ W H' => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))) =
      fun u : unip σ W H' => ((l₀ ∘ₗ e₀) ∘ₗ GlobalTheory.ConeMeasV.schrLin B.ψ w) (om (1, u.1) Ψ) := by
    funext u
    have h1 : om (1, u.1) Ψ ∈ schA F _ := hsplit.pres (1, u.1) Ψ hΨ
    have h2 := GlobalTheory.ConeMeasV.schr_mem_schA hψ w h1
    have h3 := hE.maps _ h2
    exact (hl₀eq _ h3).symm
  rw [heq]
  exact hc.comp (continuous_const.prodMk continuous_subtype_val)

end GlobalTheory.ThKSwapCont
