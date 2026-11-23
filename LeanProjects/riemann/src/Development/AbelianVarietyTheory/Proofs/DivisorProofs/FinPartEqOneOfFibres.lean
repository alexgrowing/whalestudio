import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.CMVal.Fibre

variable {E : Type} [Field E] [NumberField E]

open Classical in

theorem tendsto_of_cut (a : Af E) (g : Finset (HeightOneSpectrum (𝓞 E)) → Af E)
    (hg : ∀ T v, g T v = if v ∈ T then a v else 1) : Tendsto g atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 E)) := {v | a v ∈ v.adicCompletionIntegers E}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 E)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  have h2 := ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf
  have h3 : g = (RestrictedProduct.inclusion _ _ hle) ∘ f :=
    funext fun T => Subtype.ext (funext fun v => hg T v)
  rw [h3]
  exact h2

open Classical in

theorem prod_single_apply (y : (Af E)ˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = if v ∈ T then (y : Af E) v else 1 := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, if_neg (Finset.notMem_empty v)]; rfl
  | insert u T hu ih =>
    rw [Finset.prod_insert hu, Units.val_mul]
    change (single u (coord u y) : Af E) v * ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = _
    rw [ih]
    by_cases h : v = u
    · subst h
      rw [single_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one, coe_coord]
    · rw [suppAt_single u _ v h, one_mul]; simp [h]

theorem coord_inv' (P : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : coord P y⁻¹ = (coord P y)⁻¹ := Units.ext rfl

theorem hasProd_single (y : (Af E)ˣ) : HasProd (fun P => single P (coord P y)) y := by
  have h : ∀ y : (Af E)ˣ, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) =>
      ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E)) atTop (𝓝 (y : Af E)) := fun y =>
    tendsto_of_cut _ _ (prod_single_apply y)
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, single P (coord P y)) atTop (𝓝 y)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h y).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h y⁻¹
  simp only [coord_inv', map_inv, Finset.prod_inv_distrib] at h2
  exact h2

theorem continuous_finPart (χ : HChar E) : Continuous (finPart χ) :=
  χ.2.1.comp (Continuous.units_map (MonoidHom.inr (InfiniteAdeleRing E) (Af E)) (continuous_const.prodMk continuous_id))

theorem hasProd_loc (χ : HChar E) (y : (Af E)ˣ) : HasProd (fun P => χ.loc P (coord P y)) (finPart χ y) :=
  (hasProd_single y).map (finPart χ) (continuous_finPart χ)

theorem finPart_eq_one_of_fibres (E : Type) [Field E] [NumberField E] (χ : HChar E) (y : (Af E)ˣ)
    (h : ∀ v : HeightOneSpectrum (OF E),
      ∏ P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, χ.loc P (coord P y) = 1) : finPart χ y = 1 := by
  classical
  let U : Finset (HeightOneSpectrum (OF E)) → Finset (HeightOneSpectrum (𝓞 E)) :=
    fun S => S.biUnion (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E))
  have hmem : ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)),
      P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := fun v P => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]; rfl
  have hU : Tendsto U atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun S S' hS => Finset.biUnion_subset_biUnion_of_subset_left _ hS) fun P => ?_
    exact ⟨{P.under (OF E)}, Finset.mem_biUnion.2 ⟨_, Finset.mem_singleton_self _, (hmem _ _).2 rfl⟩⟩
  have h1 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) atTop (𝓝 (finPart χ y)) :=
    hasProd_loc χ y
  have h2 := h1.comp hU
  have h3 : ((fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) ∘ U) = fun _ => 1 := by
    funext S
    change ∏ P ∈ S.biUnion _, _ = 1
    rw [Finset.prod_biUnion]
    · exact Finset.prod_eq_one fun v _ => h v
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (hmem _ _).1 hv, ← (hmem _ _).1 hw]
  rw [h3] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

end GlobalTheory.CMVal.Fibre
