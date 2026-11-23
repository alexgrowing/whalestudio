import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakContinuityDerivativeContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseA

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeSliceMeas

open GlobalTheory.ConeMeasV GlobalTheory.ConeMeasSmall

variable {F : Type} [Field F] [NumberField F]

theorem exists_slice_map {κ : Type} [Fintype κ] (x : κ → AF F) :
    ∃ S : ((κ → AF F) → ℂ) →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ Φ ∈ schA F κ, ∀ t, S Φ t = Φ (x + GlobalTheory.ThetaTransform.embR t)) ∧
      ∀ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ, T.toLinearMap ∘ₗ S ∈ (adeleClass F).adm κ := by
  choose s hs using fun Φ : schA F κ => GlobalTheory.ConeSlice.exists_schwartz_slice Φ.2 x
  let S₀ : schA F κ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    { toFun := s
      map_add' := fun Φ Ψ => by ext t; simp [hs]
      map_smul' := fun c Φ => by ext t; simp [hs] }
  obtain ⟨S, hS⟩ := S₀.exists_extend
  have h : ∀ Φ ∈ schA F κ, ∀ t, S Φ t = Φ (x + GlobalTheory.ThetaTransform.embR t) := fun Φ hΦ t => by
    have := LinearMap.congr_fun hS ⟨Φ, hΦ⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact hs ⟨Φ, hΦ⟩ t
  refine ⟨S, h, fun T g hg => ?_⟩
  let a : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
  refine ⟨g (fun i => (x i).2) • T.comp (SchwartzMap.compSubConstCLM ℂ (-a)), fun f => ?_⟩
  have e : S (pureA F f g) = g (fun i => (x i).2) • SchwartzMap.compSubConstCLM ℂ (-a) f := by
    ext t
    rw [h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)]
    simp only [SchwartzMap.smul_apply, SchwartzMap.compSubConstCLM_apply, smul_eq_mul, pureA]
    have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + GlobalTheory.ThetaTransform.embR t) i).1) = t - -a := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) =
        t i - -a i
      rw [map_add, RingEquiv.apply_symm_apply, sub_neg_eq_add, add_comm]
    have h2 : (fun i => ((x + GlobalTheory.ThetaTransform.embR t) i).2) = fun i => (x i).2 := by
      funext i
      show (x i).2 + 0 = (x i).2
      exact add_zero _
    rw [h1, h2, mul_comm]
  show T (S (pureA F f g)) = _
  rw [e, map_smul]
  rfl

theorem stronglyMeasurable_deriv {D A L : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] (_ : SecondCountableTopology A)
    (_ : TopologicalSpace.MetrizableSpace A) [TopologicalSpace L] [MeasurableSpace L] [BorelSpace L]
    (_ : SecondCountableTopology L) (f : A → L → SchwartzMap D ℂ)
    (hA : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) l, Continuous fun k => T (f k l))
    (hL : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) k, Continuous fun l => T (f k l)) (m : ℕ) (t : D) :
    StronglyMeasurable (Function.uncurry fun k l => iteratedFDeriv ℝ m (f k l) t) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun l => GlobalTheory.WeakDeriv.continuous_iteratedFDeriv_of_weak (fun k => f k l) (fun T => hA T l) m t)
    (fun k => (GlobalTheory.WeakDeriv.continuous_iteratedFDeriv_of_weak (f k) (fun T => hL T k) m t).stronglyMeasurable)

theorem sfinite_idele {E : Type} [Field E] [NumberField E] [Algebra F E] (μ : Measure (AE F E)ˣ)
    (hμ : μ.IsHaarMeasure) : SFinite μ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI := (idele_top (F := F) (E := E)).1
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite _
  infer_instance

theorem exists_weak_family {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {b a' : ℕ}
    {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'} {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')}
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (hE : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') {Ψ : Fn F (b + 2) (b + 2 + a')}
    (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a'))) (x : Fin b × Fin (b + a') → AF F) :
    ∃ f : UA σ G.V.J → (AE F E)ˣ → SInf F (Fin b × Fin (b + a')),
      (∀ (T : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ) l, Continuous fun k => T (f k l)) ∧
      (∀ (T : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ) k, Continuous fun l => T (f k l)) ∧
      ∀ k l s, f k l s = e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) := by
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil
  obtain ⟨S, hSe, hSa⟩ := exists_slice_map x
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (b + 2 + a') → AE F E))
  have hco : Continuous G.M.co.e := IsModuleTopology.continuous_of_linearMap G.M.co.e.toLinearMap
  have hsh : Continuous (shiftA (F := F) H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Units.continuous_val.mul continuous_const
  have hadm : ∀ T : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ, (T.toLinearMap ∘ₗ S) ∘ₗ e ∈ (adeleClass F).adm _ := fun T =>
    comp_ev_mem_adm hT.geo.hM hT₁.geo.hM hE (hSa T)
  refine ⟨fun k l => S (e (schr B.ψ (G.M.co.e (shiftA H H' l)) (om (k, 1) Ψ))), fun T l => ?_, fun T k => ?_,
    fun k l s => ?_⟩
  · exact (hS.cont _ (comp_schr_mem_adm hψ (G.M.co.e (shiftA H H' l)) (hadm T)) _ hΨ).comp
      (continuous_id.prodMk continuous_const)
  · exact (continuous_schr hψ (hadm T) (hS.pres (k, 1) _ hΨ)).comp (hco.comp hsh)
  · exact hSe _ (hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΨ))) s

theorem meas_of_weak {D A L : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Group A]
    [TopologicalSpace A] [MeasurableSpace A] (_ : BorelSpace A) (hA₁ : SecondCountableTopology A)
    (hA₂ : TopologicalSpace.MetrizableSpace A) [TopologicalSpace L] [MeasurableSpace L] (_ : BorelSpace L)
    (hL₁ : SecondCountableTopology L) (K : Subgroup A) (μK : Measure K) (μ : Measure L) (_ : SFinite μ)
    (f : A → L → SchwartzMap D ℂ) (hA : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) l, Continuous fun k => T (f k l))
    (hL : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) k, Continuous fun l => T (f k l)) {c c' : L → ℂ} (hc : Continuous c)
    (hc' : Continuous c') {u : A → L → D → ℂ} (hu : ∀ k l s, f k l s = u k l s) :
    (∀ (m : ℕ) (t : D) (k : K), AEStronglyMeasurable (fun l => iteratedFDeriv ℝ m (fun s => u k.1 l s * c l * c' l) t) μ) ∧
      ∀ (m : ℕ) (t : D), AEStronglyMeasurable
        (fun k : K => ∫ l, iteratedFDeriv ℝ m (fun s => u k.1 l s * c l * c' l) t ∂μ) μK := by
  have hf : ∀ k l, (fun s => u k l s * c l * c' l) = ⇑((c l * c' l) • f k l) := fun k l => funext fun s => by
    rw [← hu, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc, mul_comm]
  simp only [hf]
  obtain ⟨g, hg⟩ : ∃ g : A → L → SchwartzMap D ℂ, ∀ k l, (c l * c' l) • f k l = g k l := ⟨_, fun _ _ => rfl⟩
  have gA : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) l, Continuous fun k => T (g k l) := fun T l => by
    simp only [← hg, map_smul, smul_eq_mul]
    exact continuous_const.mul (hA T l)
  have gL : ∀ (T : SchwartzMap D ℂ →L[ℂ] ℂ) k, Continuous fun l => T (g k l) := fun T k => by
    simp only [← hg, map_smul, smul_eq_mul]
    exact (hc.mul hc').mul (hL T k)
  simp only [hg]
  have hp : Measurable fun p : K × L => (p.1.1, p.2) := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hm : ∀ m t, StronglyMeasurable (Function.uncurry fun (k : K) l => iteratedFDeriv ℝ m (g k.1 l) t) :=
    fun m t => (stronglyMeasurable_deriv hA₁ hA₂ hL₁ g gA gL m t).comp_measurable hp
  exact ⟨fun m t k => (hm m t).of_uncurry_left.aestronglyMeasurable,
    fun m t => (hm m t).integral_prod_right.aestronglyMeasurable⟩

theorem slice_deriv_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : Fin b × Fin (b + a') → AF F,
      (∀ (m : ℕ) (t : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) (k : K), AEStronglyMeasurable (fun l : (AE F E)ˣ => iteratedFDeriv ℝ m (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) t) μ) ∧
      ∀ (m : ℕ) (t : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F), AEStronglyMeasurable (fun k : K => ∫ l, iteratedFDeriv ℝ m (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) t ∂μ) μK := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' _ e hE K μK μ _ _ hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  obtain ⟨f, ck, cl, hf⟩ := exists_weak_family hE hT hT₁ hΨ x
  obtain ⟨t1, -, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V.J
  have cν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
    continuous_subtype_val.comp (hT.chars.heckeα.1.div' hT.chars.heckeβ.1)
  have cN : Continuous fun l : (AE F E)ˣ => ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _
  exact meas_of_weak ⟨rfl⟩ t3 (metrizable_group _ t1 t4 t3) ⟨rfl⟩ (idele_top (F := F) (E := E)).1 K μK μ
    (sfinite_idele μ hμ) f ck cl cν cN
    (u := fun k l s => e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s)) hf

end GlobalTheory.ConeSliceMeas
