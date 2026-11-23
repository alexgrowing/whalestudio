import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.CdpOpenSubgroupLe
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.NotDvdSuperIndexBotOfIsProPGroup
import GroundTheory.ProfiniteCohomology.ClassFormationDefs
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Topology

universe u

section Extension

variable {G : Type u} [Group G] {H V : Subgroup G} [hVn : V.Normal]

omit hVn in
theorem inv_mul_mem_trans {a b c : G} (h₁ : a⁻¹ * b ∈ V) (h₂ : b⁻¹ * c ∈ V) : a⁻¹ * c ∈ V := by
  have := V.mul_mem h₁ h₂
  rwa [mul_assoc, mul_inv_cancel_left] at this

omit hVn in
theorem inv_mul_mem_symm {a b : G} (h : a⁻¹ * b ∈ V) : b⁻¹ * a ∈ V := by
  have := V.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem inv_mul_mem_mul {a b a' b' : G} (ha : a⁻¹ * a' ∈ V) (hb : b⁻¹ * b' ∈ V) :
    (a * b)⁻¹ * (a' * b') ∈ V := by
  have h1 : b⁻¹ * (a⁻¹ * a') * b ∈ V := by
    have := hVn.conj_mem _ ha b⁻¹
    simpa using this
  have := V.mul_mem h1 hb
  convert this using 1
  group

theorem inv_mul_mem_contractNth {n : ℕ} (j : Fin (n + 1)) {g g' : Fin (n + 1) → G}
    (h : ∀ i, (g i)⁻¹ * g' i ∈ V) (i : Fin n) :
    (Fin.contractNth j (· * ·) g i)⁻¹ * Fin.contractNth j (· * ·) g' i ∈ V := by
  simp only [Fin.contractNth]
  split_ifs
  · exact h _
  · exact inv_mul_mem_mul (h _) (h _)
  · exact h _

variable (H V) in
theorem exists_mem_inv_mul_mem {x : G} (hx : x ∈ H ⊔ V) : ∃ h ∈ H, h⁻¹ * x ∈ V := by
  obtain ⟨h, hh, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  exact ⟨h, hh, by rwa [inv_mul_cancel_left]⟩

variable (H V) in

noncomputable def supSection (x : ↥(H ⊔ V)) : ↥H :=
  ⟨(exists_mem_inv_mul_mem H V x.2).choose, (exists_mem_inv_mul_mem H V x.2).choose_spec.1⟩

variable (H V) in
theorem supSection_spec (x : ↥(H ⊔ V)) : ((supSection H V x : G))⁻¹ * x ∈ V :=
  (exists_mem_inv_mul_mem H V x.2).choose_spec.2

variable (V) in

def ConstOnCosets {X : Type*} {n : ℕ} (c : (Fin n → H) → X) : Prop :=
  ∀ x y : Fin n → H, (∀ i, ((x i : G))⁻¹ * (y i : G) ∈ V) → c x = c y

variable (V) in

noncomputable def supExtend {X : Type*} {n : ℕ} (c : (Fin n → H) → X) : (Fin n → ↥(H ⊔ V)) → X :=
  fun x => c fun i => supSection H V (x i)

theorem supExtend_eq {X : Type*} {n : ℕ} {c : (Fin n → H) → X} (hc : ConstOnCosets V c)
    (x : Fin n → ↥(H ⊔ V)) (y : Fin n → H) (hxy : ∀ i, ((y i : G))⁻¹ * (x i : G) ∈ V) :
    supExtend V c x = c y :=
  hc _ _ fun i => inv_mul_mem_trans (supSection_spec H V (x i)) (inv_mul_mem_symm (hxy i))

theorem supExtend_inclusion {X : Type*} {n : ℕ} {c : (Fin n → H) → X} (hc : ConstOnCosets V c)
    (y : Fin n → H) : supExtend V c (fun i => Subgroup.inclusion le_sup_left (y i)) = c y :=
  supExtend_eq hc _ y fun i => by simp

theorem isLocallyConstant_supExtend [TopologicalSpace G] [IsTopologicalGroup G]
    (hV : IsOpen (V : Set G)) {X : Type*} {n : ℕ} {c : (Fin n → H) → X} (hc : ConstOnCosets V c) :
    IsLocallyConstant (supExtend V c) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ i, ∀ᶠ x' in 𝓝 x, ((x i : G))⁻¹ * (x' i : G) ∈ V := fun i => by
    have hcont : Continuous fun x' : Fin n → ↥(H ⊔ V) => ((x i : G))⁻¹ * (x' i : G) :=
      continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))
    exact hcont.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simp))
  filter_upwards [Filter.eventually_all.2 hev] with x' hx'
  exact supExtend_eq hc x' _ fun i => inv_mul_mem_trans (supSection_spec H V (x i)) (hx' i)

theorem d_supExtend {k : Type u} [CommRing k] (M : Rep.{u} k G) {n : ℕ} {c : (Fin n → H) → M}
    (hc : ConstOnCosets V c) (hfix : ∀ v ∈ V, ∀ x, M.ρ v (c x) = c x) :
    (inhomogeneousCochains.d (Rep.res (H ⊔ V).subtype M) n).hom (supExtend V c) =
      supExtend V ((inhomogeneousCochains.d (Rep.res H.subtype M) n).hom c) := by
  funext x
  simp only [inhomogeneousCochains.d_hom_apply, supExtend]
  congr 1
  · change M.ρ (x 0 : G) _ = M.ρ (supSection H V (x 0) : G) _
    rw [show ((x 0 : G)) = (supSection H V (x 0) : G) * ((supSection H V (x 0) : G)⁻¹ * x 0) by
      group, map_mul, Module.End.mul_apply, hfix _ (supSection_spec H V (x 0))]
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply hc
    intro i
    refine inv_mul_mem_trans (supSection_spec H V _) ?_
    have e1 := congrFun (Fin.comp_contractNth (· * ·) (· * ·) (f := Subtype.val)
      (fun _ _ => rfl) j x) i
    have e2 := congrFun (Fin.comp_contractNth (· * ·) (· * ·) (f := Subtype.val)
      (fun _ _ => rfl) j fun i => supSection H V (x i)) i
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2]
    exact inv_mul_mem_contractNth j (fun i => inv_mul_mem_symm (supSection_spec H V (x i))) i

end Extension

section Cohomology

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (M : Rep.{u} k G) [IsDiscreteRep M]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsDiscreteRep M] in
theorem constOnCosets_mono {H : Subgroup G} {V V' : Subgroup G} (h : V' ≤ V) {X : Type*} {n : ℕ}
    {c : (Fin n → H) → X} (hc : ConstOnCosets V c) : ConstOnCosets V' c :=
  fun x y hxy => hc x y fun i => h (hxy i)

theorem exists_openNormalSubgroup_constOnCosets {H : Subgroup G} (hH : IsClosed (H : Set G))
    {n : ℕ} {c : (Fin n → H) → M} (hc : IsLocallyConstant c) :
    ∃ V : OpenNormalSubgroup G, ConstOnCosets (V : Subgroup G) c ∧
      ∀ v ∈ (V : Subgroup G), ∀ x, M.ρ v (c x) = c x := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨W, hW⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hc
  obtain ⟨V₂, hV₂⟩ := exists_subgroupOf_le W
  have hdisc := (isDiscreteRep_iff_forall_exists_openNormalSubgroup M).1 inferInstance
  choose Um hUm using hdisc
  have : Finite (Set.range c) := hc.range_finite.to_subtype
  obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite
    (fun o : Option (Set.range c) => o.elim V₂ fun m => Um m.1)
  refine ⟨V, fun x y hxy => hW x y fun i => hV₂ ?_, fun v hv x => ?_⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hV none (hxy i)
  · exact (Representation.mem_invariants _ _).1 (hUm (c x)) ⟨v, hV (some ⟨c x, x, rfl⟩) hv⟩

theorem exists_cohomologyResLE_eq {H : Subgroup G} (hH : IsClosed (H : Set G)) (q : ℕ)
    (x : cohomology (Rep.res H.subtype M) q) :
    ∃ (U : Subgroup G) (_ : IsOpen (U : Set G)) (hHU : H ≤ U)
      (y : cohomology (Rep.res U.subtype M) q), (cohomologyResLE M hHU q).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (Rep.res H.subtype M)).homologyπ q)).1 inferInstance x
  let f : locallyConstantCochains (Rep.res H.subtype M) q :=
    ((cochainsComplex (Rep.res H.subtype M)).iCycles q).hom z
  have hflc : IsLocallyConstant f.1 := f.2
  have hdf : (inhomogeneousCochains.d (Rep.res H.subtype M) q).hom f.1 = 0 := by
    have := iCycles_d_apply (cochainsComplex (Rep.res H.subtype M)) q (q + 1) z
    rw [cochainsComplex_d] at this
    exact congrArg Subtype.val this
  obtain ⟨V, hVc, hVfix⟩ := exists_openNormalSubgroup_constOnCosets M hH hflc
  set U := H ⊔ (V : Subgroup G) with hUdef
  have hUo : IsOpen (U : Set G) := Subgroup.isOpen_mono le_sup_right V.isOpen'
  let F : locallyConstantCochains (Rep.res U.subtype M) q :=
    ⟨supExtend (V : Subgroup G) f.1, isLocallyConstant_supExtend V.isOpen' hVc⟩
  have hF : ((cochainsComplex (Rep.res U.subtype M)).d q
      ((ComplexShape.up ℕ).next q)).hom F = 0 := by
    rw [show (ComplexShape.up ℕ).next q = q + 1 by simp, cochainsComplex_d]
    apply Subtype.ext
    change (inhomogeneousCochains.d (Rep.res U.subtype M) q).hom
      (supExtend (H := H) (V : Subgroup G) f.1) = 0
    rw [d_supExtend M hVc hVfix, hdf]
    rfl
  obtain ⟨zF, hzF⟩ := exists_iCycles_eq (cochainsComplex (Rep.res U.subtype M)) F hF
  refine ⟨U, hUo, le_sup_left, ((cochainsComplex _).homologyπ q).hom zF, ?_⟩
  change (HomologicalComplex.homologyMap (cochainsMapAlong (Subgroup.inclusion (le_sup_left : H ≤ U))
    (continuous_subgroup_inclusion _) (resResHom M _)) q).hom
      (((cochainsComplex _).homologyπ q).hom zF) = _
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (Rep.res H.subtype M)).iCycles q)).1
    inferInstance
  rw [iCycles_cyclesMap_apply, hzF]
  apply Subtype.ext
  funext h
  exact supExtend_inclusion hVc h

theorem exists_cohomologyRes_eq_zero {H : Subgroup G} (hH : IsClosed (H : Set G)) (q : ℕ)
    (x : cohomology M (q + 1)) (hx : (cohomologyRes M H (q + 1)).hom x = 0) :
    ∃ (U : Subgroup G) (_ : IsOpen (U : Set G)) (_ : H ≤ U),
      (cohomologyRes M U (q + 1)).hom x = 0 := by
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex M).homologyπ (q + 1))).1 inferInstance x
  let f : locallyConstantCochains M (q + 1) := ((cochainsComplex M).iCycles (q + 1)).hom z
  have hx' : ((cochainsComplex (Rep.res H.subtype M)).homologyπ (q + 1)).hom
      ((HomologicalComplex.cyclesMap (cochainsMapAlong H.subtype (continuous_subgroup_subtype H)
        (𝟙 _)) (q + 1)).hom z) = 0 := by
    rw [← homologyMap_homologyπ_apply]
    exact hx
  obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff _ _).1 hx'
  rw [iCycles_cyclesMap_apply] at hw
  generalize hj : (ComplexShape.up ℕ).prev (q + 1) = j at w hw
  have hjq : j = q := by
    rw [← hj]
    simp
  subst hjq
  have hwlc : IsLocallyConstant (w : locallyConstantCochains (Rep.res H.subtype M) j).1 := w.2
  obtain ⟨V₁, hV₁c, hV₁fix⟩ := exists_openNormalSubgroup_constOnCosets M hH hwlc
  obtain ⟨V₂, hV₂⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant f.2
  obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite (fun b : Bool => if b then V₁ else V₂)
  set c := (w : locallyConstantCochains (Rep.res H.subtype M) j).1 with hcdef
  have hVc : ConstOnCosets (V : Subgroup G) c := constOnCosets_mono (hV true) hV₁c
  have hVfix : ∀ v ∈ (V : Subgroup G), ∀ x, M.ρ v (c x) = c x :=
    fun v hv => hV₁fix v (hV true hv)
  set U := H ⊔ (V : Subgroup G) with hUdef
  let w' : locallyConstantCochains (Rep.res U.subtype M) j :=
    ⟨supExtend (V : Subgroup G) c, isLocallyConstant_supExtend V.isOpen' hVc⟩
  refine ⟨U, Subgroup.isOpen_mono le_sup_right V.isOpen', le_sup_left, ?_⟩
  change (HomologicalComplex.homologyMap (cochainsMapAlong U.subtype (continuous_subgroup_subtype U)
    (𝟙 _)) (j + 1)).hom (((cochainsComplex M).homologyπ (j + 1)).hom z) = 0
  rw [homologyMap_homologyπ_apply]
  have hcyc : (HomologicalComplex.cyclesMap (cochainsMapAlong U.subtype
      (continuous_subgroup_subtype U) (𝟙 _)) (j + 1)).hom z =
      ((cochainsComplex _).toCycles j (j + 1)).hom w' := by
    apply (ModuleCat.mono_iff_injective ((cochainsComplex _).iCycles (j + 1))).1 inferInstance
    rw [iCycles_cyclesMap_apply]
    rw [show ((cochainsComplex (Rep.res U.subtype M)).iCycles (j + 1)).hom
      (((cochainsComplex _).toCycles j (j + 1)).hom w') =
        ((cochainsComplex _).d j (j + 1)).hom w' from
      congrArg (fun φ => ModuleCat.Hom.hom φ w') ((cochainsComplex _).toCycles_i j (j + 1))]
    rw [cochainsComplex_d]
    apply Subtype.ext
    change _ = (inhomogeneousCochains.d (Rep.res U.subtype M) j).hom
      (supExtend (H := H) (V : Subgroup G) c)
    rw [d_supExtend M hVc hVfix]
    have hw' : (inhomogeneousCochains.d (Rep.res H.subtype M) j).hom c =
        fun h => f.1 fun i => (h i : G) := by
      rw [cochainsComplex_d] at hw
      exact congrArg Subtype.val hw
    rw [hw']
    funext u
    change f.1 (fun i => (u i : G)) = f.1 fun i => (supSection H (V : Subgroup G) (u i) : G)
    exact hV₂ _ _ fun i => hV false (inv_mul_mem_symm (supSection_spec H (V : Subgroup G) (u i)))
  rw [hcyc]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ w')
    ((cochainsComplex _).toCycles_comp_homologyπ j (j + 1))

end Cohomology

end GroundTheory.ProfCoh
