import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.Adele.IdeleBasis

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem eventually_finiteProj_mem_units (x : IdeleGroup K) :
    ∀ᶠ v in cofinite, finiteProj v x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  filter_upwards [(prodRestrictedEquiv K x).2.2] with v hv
  rw [finiteProj_eq]
  exact hv

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)

theorem hasFiniteMulSupport
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
    (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ φ v (finiteProj v x) := by
  have h : ∀ᶠ v in cofinite, φ v (finiteProj v x) = 1 := by
    filter_upwards [hφ, eventually_finiteProj_mem_units x] with v hv hx
    exact hv hx
  exact eventually_cofinite.1 h

def ideleMap
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker) :
    IdeleGroup K →* G where
  toFun x := (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [finprod_mul_distrib (hasFiniteMulSupport φ hφ x) (hasFiniteMulSupport φ hφ y),
      Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem ideleMap_apply (x : IdeleGroup K) :
    ideleMap φ φinf hφ x = (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x) :=
  rfl

@[simp]
theorem ideleMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleMap φ φinf hφ (finiteEmbedding v a) = φ v a := by
  rw [ideleMap_apply, finprod_eq_single _ v fun u hu ↦ by
    rw [finiteProj_finiteEmbedding_of_ne hu, map_one]]
  have h : ∀ w, infiniteProj w (finiteEmbedding v a) = 1 := fun w ↦ Units.ext rfl
  simp [h]

@[simp]
theorem ideleMap_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleMap φ φinf hφ (infiniteEmbedding w a) = φinf w a := by
  rw [ideleMap_apply, Finset.prod_eq_single w (fun u _ hu ↦ by
    rw [infiniteProj_infiniteEmbedding_of_ne hu, map_one]) (fun h ↦ (h (Finset.mem_univ w)).elim)]
  have h : ∀ v, finiteProj v (infiniteEmbedding w a) = 1 := fun v ↦ Units.ext rfl
  simp [h]

theorem ideleMap_comp_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    (ideleMap φ φinf hφ).comp (finiteEmbedding v) = φ v :=
  MonoidHom.ext (ideleMap_finiteEmbedding φ φinf hφ v)

theorem ideleMap_comp_infiniteEmbedding (w : InfinitePlace K) :
    (ideleMap φ φinf hφ).comp (infiniteEmbedding w) = φinf w :=
  MonoidHom.ext (ideleMap_infiniteEmbedding φ φinf hφ w)

theorem ideleMap_eq_one_of_forall_mem
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (Ninf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
    (hN : ∀ v, N v ≤ (φ v).ker) (hNinf : ∀ w, Ninf w ≤ (φinf w).ker) {x : IdeleGroup K}
    (hx : ∀ v, finiteProj v x ∈ N v) (hxinf : ∀ w, infiniteProj w x ∈ Ninf w) :
    ideleMap φ φinf hφ x = 1 := by
  rw [ideleMap_apply, finprod_eq_one_of_forall_eq_one fun v ↦ hN v (hx v),
    Finset.prod_eq_one fun w _ ↦ hNinf w (hxinf w), mul_one]

variable [TopologicalSpace G] [DiscreteTopology G]

theorem continuous_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) :
    Continuous (ideleMap φ φinf hφ) := by
  have hker : ∀ {X : Type _} [TopologicalSpace X] [Group X] (f : X →* G), Continuous f →
      IsOpen (f.ker : Set X) := fun f hf ↦ by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} : Set G)).preimage hf
  set V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∩
      ((φ v).ker : Set (v.adicCompletion K)ˣ) with hVdef
  set W : Set (IdeleGroup K) :=
    {x | (∀ w, infiniteProj w x ∈ ((φinf w).ker : Set (w.Completion)ˣ)) ∧
      ∀ v, finiteProj v x ∈ V v} with hWdef
  have hWo : IsOpen W := (isTopologicalBasis K).isOpen
    ⟨fun w ↦ ((φinf w).ker : Set (w.Completion)ˣ), V, fun w ↦ hker _ (hφinfc w),
      fun v ↦ (isOpen_units_adicCompletionIntegers K v).inter (hker _ (hφc v)),
      hφ.mono fun v hv ↦ Set.inter_eq_left.2 (SetLike.coe_subset_coe.2 hv), rfl⟩
  have h1W : (1 : IdeleGroup K) ∈ W :=
    ⟨fun w ↦ by simp, fun v ↦ by simp [V]⟩
  have hψW : ∀ x ∈ W, ideleMap φ φinf hφ x = 1 := fun x hx ↦
    ideleMap_eq_one_of_forall_mem φ φinf hφ (fun v ↦ (φ v).ker) (fun w ↦ (φinf w).ker)
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun v ↦ (hx.2 v).2) hx.1
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, nhds_discrete G, tendsto_pure]
  exact eventually_of_mem (hWo.mem_nhds h1W) hψW

def continuousIdeleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) :
    IdeleGroup K →ₜ* G where
  toMonoidHom := ideleMap φ φinf hφ
  continuous_toFun := continuous_ideleMap φ φinf hφ hφc hφinfc

@[simp]
theorem continuousIdeleMap_apply (hφc : ∀ v, Continuous (φ v))
    (hφinfc : ∀ w, Continuous (φinf w)) (x : IdeleGroup K) :
    continuousIdeleMap φ φinf hφ hφc hφinfc x = ideleMap φ φinf hφ x :=
  rfl

end IdeleMap

end

end GroundTheory.Global
