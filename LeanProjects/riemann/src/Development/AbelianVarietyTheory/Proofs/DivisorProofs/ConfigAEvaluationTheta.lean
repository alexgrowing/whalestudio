import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationTripleUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigFirstEvalCharCompatStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKNScalar

section
open scoped Classical

theorem proj_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → AF F) :
    (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (y i))).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.coe_proj, Function.eval, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, pureA]
  rw [mul_comm]
  rfl

end

theorem twist_scalar : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (k : UA σ G.V.J) (a : AE F E), mat k *ᵥ incV F H.x = a • incV F H.x →
    (∀ z : Fin b → AE F E, ∃ c : AE F E, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + c • incV F H.x) →
    ∃ c : ℂ, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (om (k, 1) Ψ) = c • e Ψ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ k a hx hι
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hP₁ := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).1
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨h1, h2⟩ := GlobalTheory.T.eval_comp_om_rho_equivariant_isoA_invariant F E σ B b a' G G₁ H H' hC e he X om om' hT k a hx hι
  refine GlobalTheory.T.config_first_eval_char_compat hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ (e ∘ₗ om (k, 1)) h1 h2 fun y => ?_
  have := hS.adm (k, 1) _ (GlobalTheory.T.eigen_intertwiner_good_models F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι _ e hP.good hP₁.good he _
    (proj_adm F _ y))
  rwa [LinearMap.comp_assoc] at this

end GlobalTheory.ThKNScalar

end
