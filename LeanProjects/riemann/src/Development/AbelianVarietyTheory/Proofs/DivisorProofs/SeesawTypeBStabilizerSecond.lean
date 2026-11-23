import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical nonZeroDivisors
open GlobalTheory.Doubling (absE)
open GlobalTheory.LocIdeal (locId)

noncomputable section

namespace GlobalTheory.ConeMeasPure

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

theorem coneInt_pure_stronglyMeasurable : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
    ∀ y : Fin b × Fin (a + b) → AF F,
      StronglyMeasurable (Function.uncurry fun (k : K) (l : (AE F E)ˣ) =>
        coneInt B G.M' om' e' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) k.1 l y) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K _ X om om' om₁ om₁' hT hT₁ ei ev _ _ _ f φ hφ hφc y
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΦA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F _ :=
    GlobalTheory.TensUniq.pure_mem_schA f φ hφ ((hφc.and hM.std).mono fun v hv => hv.1.trans hv.2)
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  obtain ⟨v1, v2⟩ := GlobalTheory.ConeMeasSmall.idele_top (F := F) (E := E)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V'.J) := GlobalTheory.ConeMeasSmall.metrizable_group _ t1 t4 t3
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  have hco : Continuous G.M'.co.e := IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hsh : Continuous (shiftB σ H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hcA.comp Units.continuous_val).mul continuous_const
  have hadm := GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE (proj_mem_adm F _ y)
  have hν0 : Continuous (X.ν) := by
    show Continuous fun x => X.α x / X.β x
    exact hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  have hν : Continuous fun l : (AE F E)ˣ => ((X.ν l : Circle) : ℂ) := continuous_subtype_val.comp hν0
  have habs : Continuous fun l : (AE F E)ˣ => (((absE F E l : NNReal) : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _
  have ck : ∀ l : (AE F E)ˣ, Continuous fun k : K =>
      coneInt B G.M' om' e' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) k.1 l y := by
    intro l
    have h1 := (hS.cont _ (GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' l)) hadm) _ hΦA).comp
      (continuous_subtype_val.prodMk continuous_const : Continuous fun k : K => ((k.1, (1 : UA σ G.W.J))))
    exact (h1.mul continuous_const).mul continuous_const
  have cl : ∀ k : K, Continuous fun l : (AE F E)ˣ =>
      coneInt B G.M' om' e' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) k.1 l y := by
    intro k
    have h1 := (GlobalTheory.ConeMeasSmall.continuous_schr hψ hadm (hS.pres (k.1, 1) _ hΦA)).comp (hco.comp hsh)
    exact (h1.mul hν).mul habs
  haveI : TopologicalSpace.MetrizableSpace K := Topology.IsEmbedding.subtypeVal.metrizableSpace
  haveI : SecondCountableTopology K := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : BorelSpace K := Subtype.borelSpace _
  exact (measurable_uncurry_of_continuous_of_measurable ck fun k => (cl k).measurable).stronglyMeasurable

end GlobalTheory.ConeMeasPure

end
