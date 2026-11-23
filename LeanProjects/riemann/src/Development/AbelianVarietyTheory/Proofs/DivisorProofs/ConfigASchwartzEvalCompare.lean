import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ConeIntCont

open scoped Classical in

theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem continuous_coneIntegrand : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ (l : (AE F E)ˣ) (y : Fin b × Fin (b + a') → AF F),
      Continuous fun g : UA σ G.V.J => e (G.M.co.rho B.ψ (shiftA H H' l) (om (g, 1) Ψ)) y := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ e hE X om om' om₁ om₁' hT hT₁ Ψ hΨ l y
  have hM := hT.geo.hM
  have hM₁ := hT₁.geo.hM
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hadm := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (G.M.co.e (shiftA H H' l))
    (GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE (proj_mem_adm F _ y))
  exact (hS.cont _ hadm _ hΨ).comp (continuous_id.prodMk continuous_const)

end GlobalTheory.ThK.ConeIntCont

end
