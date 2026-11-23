import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeStabP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProduStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvZeroAdm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ y, (LinearMap.proj y : Fn F n d₁ →ₗ[ℂ] ℂ).comp e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he y
  obtain ⟨ei, ev, -, -, hloc⟩ := he.loc
  let δ : SInf F (Fin n × Fin d₁) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (y i))).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
  have hδ : ∀ h : SInf F (Fin n × Fin d₁), δ h = h (fun i => evI F (y i)) := fun _ => rfl
  have hev : ∀ (v : Pl F) (a : AF F), evFin F v a = evalV F v a.2 := fun _ _ => rfl
  intro g hg

  refine Submodule.span_induction (p := fun g _ => ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ,
      ∀ f : SInf F (Fin n × Fin d), ((LinearMap.proj y : Fn F n d₁ →ₗ[ℂ] ℂ).comp e) (pureA F f g) = T f)
    ?_ ?_ ?_ ?_ (GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F (Fin n × Fin d) g hg)
  · rintro _ ⟨φ, hφ, hφstd, rfl⟩
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hφstd, hP.good.std] with v h1 h2
      rw [h1, h2]
    have hpure : ∀ f : SInf F (Fin n × Fin d),
        pureA F f (fun x => ∏ᶠ v, φ v fun i => evalV F v (x i)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
      intro f
      funext x
      simp only [pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hev, evI]
    refine ⟨(∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))) • (δ.comp ei), fun f => ?_⟩
    rw [LinearMap.comp_apply, hpure f, hloc f φ hφ hvac]
    simp only [LinearMap.proj_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hδ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, smul_eq_mul]
    ring
  · refine ⟨0, fun f => ?_⟩
    have : pureA F f (0 : (Fin n × Fin d → Af F) → ℂ) = 0 := by
      funext x
      simp [pureA]
    rw [this, map_zero, ContinuousLinearMap.zero_apply]
  · rintro g₁ g₂ - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    refine ⟨T₁ + T₂, fun f => ?_⟩
    have : pureA F f (g₁ + g₂) = pureA F f g₁ + pureA F f g₂ := by
      funext x
      simp [pureA, mul_add]
    rw [this, map_add, h₁, h₂, ContinuousLinearMap.add_apply]
  · rintro a g₁ - ⟨T₁, h₁⟩
    refine ⟨a • T₁, fun f => ?_⟩
    have : pureA F f (a • g₁) = a • pureA F f g₁ := by
      funext x
      simp only [pureA, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, map_smul, h₁, ContinuousLinearMap.smul_apply]

end GlobalTheory.EvZeroAdm

end
