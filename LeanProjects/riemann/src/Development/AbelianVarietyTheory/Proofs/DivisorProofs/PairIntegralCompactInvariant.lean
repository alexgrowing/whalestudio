import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLocalFinitePlacesProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseAdeleExtInfiniteFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryIdempotentTendstoStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TailFix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evalAdm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  classical
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  rw [LinearMap.proj_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.TailFix

open GlobalTheory.TailFix in

theorem GlobalTheory.TailFix.fix_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (T : Finset (Pl F)) (k : UA σ W.J), k ∈ UAt σ W (fun u : AF F => u.2) →
    (∀ v ∈ T, ∀ u : AF F, At (evFin F v) u → u • mat k = u • (1 : Matrix (Fin d) (Fin d) (AE F E))) →
    (∀ v ∉ T, ∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat k) →
      Acts (evFin F v) (om (1, g)) (M.vac v) (M.vac v)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ v ∉ T, φ v = M.vac v) → om (1, k) (pure f φ) = pure f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP T k hk hT hvac f φ hφ hφT
  classical
  have hcof : ∀ᶠ v in Filter.cofinite, φ v = M.vac v :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (hφT v h))
  have hActs : ∀ v, Acts (evFin F v) (om (1, locU v k)) (φ v) (φ v) := by
    intro v
    by_cases hv : v ∈ T
    · rw [locU_eq_one v k (hT v hv)]
      intro r _
      rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]
      rfl
    · rw [hφT v hv]
      exact hvac v hv (locU v k) (locU_mem v k) (locU_eq v k)
  have hA : ∀ S : Finset (Pl F), om (1, splU (idem S) (idem_mul_self S) k) (pure f φ) = pure f φ := by
    intro S
    have e : splU (idem S) (idem_mul_self S) k = (S.toList.map fun v => locU v k).prod := by
      refine (UA_ext ?_).trans (splU_toFinset k S.toList S.nodup_toList)
      rw [mat_splU, mat_splU, Finset.toList_toFinset]
    rw [e]
    exact GlobalTheory.T.pair_local_finite_places_product F E σ B n d X W M χX χW om r s r' s' hP S.toList S.nodup_toList (fun v => locU v k)
      (fun v _ => locU_mem v k) f φ φ hφ hcof (fun v _ => ⟨hφ v, hActs v⟩) (fun _ _ => rfl)
  funext x
  have hc : Continuous fun g : UA σ X.J × UA σ W.J => LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) x (om g (pure f φ)) :=
    hP.weil.2.2 _ (evalAdm x) _ (GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hφ hcof)
  have ht : Tendsto (fun S : Finset (Pl F) => ((1 : UA σ X.J), splU (idem S) (idem_mul_self S) k)) atTop (𝓝 (1, k)) :=
    tendsto_const_nhds.prodMk_nhds (GlobalTheory.T.split_unitary_idempotent_tendsto k hk)
  have h2 := (hc.tendsto _).comp ht
  simp only [Function.comp_def, LinearMap.proj_apply, hA] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds
