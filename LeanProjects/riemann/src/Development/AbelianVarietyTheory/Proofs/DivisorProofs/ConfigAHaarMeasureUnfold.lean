import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigASchwartzEvalEqual

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeRatPtMeas

open GlobalTheory.ConeMeasV GlobalTheory.ConeMeasSmall GlobalTheory.ConeIdeleMeas

theorem aestronglyMeasurable_ratPt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      ∀ ξ : Fin b × Fin (b + a') → F, AEStronglyMeasurable (fun p : K × (AE F E)ˣ =>
        om₁ x (e (G.M.co.rho B.ψ (shiftA H H' p.2) (om (p.1.1, 1) Ψ))) (fun i => algebraMap F (AF F) (ξ i))) (μK.prod μ) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' _ K μK μ _ _ _ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x ξ
  have hM := hT.geo.hM
  have hM₁ := hT₁.geo.hM
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hS₁ := IsUWeilPair.isUSplitting hT₁.weil
  obtain ⟨L, hadm, hL⟩ : ∃ L ∈ (adeleClass F).adm (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ Φ, L Φ = om₁ x (e Φ) (fun i => algebraMap F (AF F) (ξ i)) :=
    ⟨((LinearMap.proj (fun i => algebraMap F (AF F) (ξ i)) : Fn F b (b + a') →ₗ[ℂ] ℂ) ∘ₗ om₁ x) ∘ₗ e,
      comp_ev_mem_adm hM hM₁ he (hS₁.adm x _ (proj_mem_adm F _ _)), fun _ => rfl⟩
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V.J) := metrizable_group _ t1 t4 t3
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (b + 2 + a') → AE F E))
  have hco : Continuous G.M.co.e := IsModuleTopology.continuous_of_linearMap G.M.co.e.toLinearMap
  have hsh : Continuous (shiftA (F := F) H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Units.continuous_val.mul continuous_const
  let u : UA σ G.V.J → (AE F E)ˣ → ℂ := fun k l => L (schr B.ψ (G.M.co.e (shiftA H H' l)) (om (k, 1) Ψ))
  have ck : ∀ l, Continuous fun k => u k l := fun l =>
    (hS.cont _ (comp_schr_mem_adm hψ (G.M.co.e (shiftA H H' l)) hadm) _ hΨ).comp
      (continuous_id.prodMk continuous_const)
  have cl : ∀ k, Continuous (u k) := fun k =>
    (continuous_schr hψ hadm (hS.pres (k, 1) _ hΨ)).comp (hco.comp hsh)
  have m1 : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable ck fun k => (cl k).measurable
  have q2 : Measurable fun p : K × (AE F E)ˣ => ((p.1.1 : UA σ G.V.J), p.2) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have m2 : Measurable ((Function.uncurry u) ∘ fun p : K × (AE F E)ˣ => ((p.1.1 : UA σ G.V.J), p.2)) := m1.comp q2
  have key : ∀ p : K × (AE F E)ˣ, ((Function.uncurry u) ∘ fun p : K × (AE F E)ˣ => ((p.1.1 : UA σ G.V.J), p.2)) p =
      om₁ x (e (G.M.co.rho B.ψ (shiftA H H' p.2) (om (p.1.1, 1) Ψ))) (fun i => algebraMap F (AF F) (ξ i)) := fun p => by
    rw [Function.comp_apply, Function.uncurry_apply_pair]
    exact hL _
  refine StronglyMeasurable.aestronglyMeasurable ?_
  exact (funext key) ▸ m2.stronglyMeasurable

end GlobalTheory.ConeRatPtMeas

end
