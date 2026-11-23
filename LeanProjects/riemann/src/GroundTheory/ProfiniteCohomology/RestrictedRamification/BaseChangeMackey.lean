import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangePlaces
import GroundTheory.ProfiniteCohomology.MackeyFormula.CompactSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.SemiLocal

universe u

noncomputable section

section Family

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  (S : Set (HeightOneSpectrum (𝓞 F)))
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

def gsFinFamily (v : S) :
    Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) /
      (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) →ₜ* galUnramifiedOutside F Ω S :=
  ⟨decompHomS ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) S (ιs v),
    continuous_decompHomS (Kv := (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) S (ιs v)⟩

theorem gsFinFamily_apply (v : S)
    (σ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) /
      (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) (y : maxUnramifiedOutside F Ω S) :
    ιs v ((gsFinFamily S ιs v σ y : maxUnramifiedOutside F Ω S) : Ω) = σ (ιs v y) :=
  decompHom_apply ((ιs v).comp (maxUnramifiedOutside F Ω S).val) σ y

end Family

section SubgroupCongr

variable {H : Type*} [Group H] [TopologicalSpace H]

def continuousMulEquivOfSubgroupEq {A B : Subgroup H} (h : A = B) : A ≃ₜ* B :=
  { MulEquiv.subgroupCongr h with
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }

end SubgroupCongr

section Fixing

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  {v : HeightOneSpectrum (𝓞 F)} (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))

def closureEquivOfAlgHom : AlgebraicClosure (v.adicCompletion F) ≃+*
    AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) :=
  letI : Algebra ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F)) :=
    (completionEmbeddingOfAlgHom j).toRingHom.toAlgebra
  haveI : IsScalarTower (v.adicCompletion F) ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure (v.adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a => ((completionEmbeddingOfAlgHom j).commutes a).symm
  haveI : Algebra.IsAlgebraic ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure (v.adicCompletion F)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion F) ((placeOfAlgHom j).1.adicCompletion L)
  haveI : IsAlgClosure ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F)) :=
    ⟨inferInstance, inferInstance⟩
  (IsAlgClosure.equiv ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F))
    (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L))).toRingEquiv

theorem closureEquivOfAlgHom_completionEmbedding (y : (placeOfAlgHom j).1.adicCompletion L) :
    closureEquivOfAlgHom j (completionEmbeddingOfAlgHom j y) =
      algebraMap _ (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) y := by
  let _ : Algebra ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F)) :=
    (completionEmbeddingOfAlgHom j).toRingHom.toAlgebra
  exact AlgEquiv.commutes _ y

theorem closureEquivOfAlgHom_symm_algebraMap (y : (placeOfAlgHom j).1.adicCompletion L) :
    (closureEquivOfAlgHom j).symm
        (algebraMap _ (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) y) =
      completionEmbeddingOfAlgHom j y :=
  (closureEquivOfAlgHom j).symm_apply_eq.2 (closureEquivOfAlgHom_completionEmbedding j y).symm

def fixingOfAlgHom : Subgroup Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F) where
  carrier := {σ | ∀ l, σ (j l) = j l}
  mul_mem' {a b} ha hb l := by
    change a (b (j l)) = j l
    rw [hb l, ha l]
  one_mem' _ := rfl
  inv_mem' {σ} hσ l := by
    rw [AlgEquiv.aut_inv]
    exact σ.symm_apply_eq.2 (hσ l).symm

omit [NumberField L] in
theorem mem_fixingOfAlgHom_iff (σ : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) :
    σ ∈ fixingOfAlgHom j ↔ ∀ l, σ (j l) = j l :=
  Iff.rfl

def fixingOfAlgHomToAut (σ : fixingOfAlgHom j) :
    Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) / (placeOfAlgHom j).1.adicCompletion L) :=
  AlgEquiv.ofRingEquiv (f := ((closureEquivOfAlgHom j).symm.trans σ.1.toRingEquiv).trans
      (closureEquivOfAlgHom j)) fun y => by
    change closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm (algebraMap _ _ y))) = _
    rw [closureEquivOfAlgHom_symm_algebraMap, apply_completionEmbeddingOfAlgHom_of_forall j σ.1 σ.2,
      closureEquivOfAlgHom_completionEmbedding]

def autToFixingOfAlgHom
    (τ : Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L)) : fixingOfAlgHom j :=
  ⟨AlgEquiv.ofRingEquiv (f := ((closureEquivOfAlgHom j).trans τ.toRingEquiv).trans
      (closureEquivOfAlgHom j).symm) fun a => by
    change (closureEquivOfAlgHom j).symm (τ (closureEquivOfAlgHom j (algebraMap _ _ a))) = _
    rw [← (completionEmbeddingOfAlgHom j).commutes a, closureEquivOfAlgHom_completionEmbedding,
      τ.commutes, closureEquivOfAlgHom_symm_algebraMap],
   fun l => by
    change (closureEquivOfAlgHom j).symm (τ (closureEquivOfAlgHom j (j l))) = j l
    rw [← completionEmbeddingOfAlgHom_algebraMap j l, closureEquivOfAlgHom_completionEmbedding,
      τ.commutes, closureEquivOfAlgHom_symm_algebraMap]⟩

def fixingOfAlgHomMulEquiv : fixingOfAlgHom j ≃*
    Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) / (placeOfAlgHom j).1.adicCompletion L) where
  toFun := fixingOfAlgHomToAut j
  invFun := autToFixingOfAlgHom j
  left_inv σ := Subtype.ext (AlgEquiv.ext fun z => by
    change (closureEquivOfAlgHom j).symm (closureEquivOfAlgHom j
      (σ.1 ((closureEquivOfAlgHom j).symm (closureEquivOfAlgHom j z)))) = σ.1 z
    simp)
  right_inv τ := AlgEquiv.ext fun z => by
    change closureEquivOfAlgHom j ((closureEquivOfAlgHom j).symm
      (τ (closureEquivOfAlgHom j ((closureEquivOfAlgHom j).symm z)))) = τ z
    simp
  map_mul' σ τ := AlgEquiv.ext fun z => by
    change closureEquivOfAlgHom j (σ.1 (τ.1 ((closureEquivOfAlgHom j).symm z))) =
      closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm (closureEquivOfAlgHom j
        (τ.1 ((closureEquivOfAlgHom j).symm z)))))
    simp

theorem fixingOfAlgHomMulEquiv_apply (σ : fixingOfAlgHom j)
    (z : AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) :
    fixingOfAlgHomMulEquiv j σ z =
      closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm z)) :=
  rfl

theorem continuous_coe_fixingOfAlgHomMulEquiv_symm :
    Continuous fun τ : Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
        (placeOfAlgHom j).1.adicCompletion L) =>
      (((fixingOfAlgHomMulEquiv j).symm τ : fixingOfAlgHom j) :
        Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) := by
  let f : Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L) →*
      Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F) :=
    (fixingOfAlgHom j).subtype.comp (fixingOfAlgHomMulEquiv j).symm.toMonoidHom
  change Continuous f
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff (v.adicCompletion F)
    (AlgebraicClosure (v.adicCompletion F)) s).1 hs
  classical
  let b := Module.finBasis (v.adicCompletion F) K
  let K' : IntermediateField ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) :=
    IntermediateField.adjoin _ (Set.range fun i => closureEquivOfAlgHom j (b i : _))
  have hK' : FiniteDimensional ((placeOfAlgHom j).1.adicCompletion L) K' :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((krullTopology_mem_nhds_one_iff _ _ _).2 ⟨K', hK', le_rfl⟩)
    fun τ hτ => hKs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  have hb : ∀ i, f τ (b i : AlgebraicClosure (v.adicCompletion F)) = b i := fun i => by
    change (closureEquivOfAlgHom j).symm (τ (closureEquivOfAlgHom j (b i : _))) = b i
    rw [hτ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩), RingEquiv.symm_apply_apply]
  intro y hy
  have hlin : ((f τ).toLinearMap ∘ₗ K.val.toLinearMap :
      K →ₗ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) = K.val.toLinearMap :=
    b.ext fun i => hb i
  exact LinearMap.congr_fun hlin ⟨y, hy⟩

def fixingOfAlgHomEquiv : fixingOfAlgHom j ≃ₜ*
    Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) / (placeOfAlgHom j).1.adicCompletion L) :=
  have hc : Continuous (fixingOfAlgHomMulEquiv j).symm :=
    (continuous_coe_fixingOfAlgHomMulEquiv_symm j).subtype_mk _
  let e := hc.homeoOfEquivCompactToT2 (f := (fixingOfAlgHomMulEquiv j).symm.toEquiv)
  { fixingOfAlgHomMulEquiv j with
    continuous_toFun := e.symm.continuous
    continuous_invFun := hc }

theorem fixingOfAlgHomEquiv_apply (σ : fixingOfAlgHom j)
    (z : AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) :
    fixingOfAlgHomEquiv j σ z = closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm z)) :=
  rfl

end Fixing

section Mackey

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

def gsLocalEmbedding (v : S) (x : galUnramifiedOutside F Ω S) :
    L →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :=
  ((ιs v).comp ((maxUnramifiedOutside F Ω S).val.comp (x⁻¹ : galUnramifiedOutside F Ω S).toAlgHom)).comp
    (gsEmbedding hL)

theorem gsLocalEmbedding_apply (v : S) (x : galUnramifiedOutside F Ω S) (l : L) :
    gsLocalEmbedding hL ιs v x l =
      ιs v ((((x⁻¹ : galUnramifiedOutside F Ω S) (gsEmbedding hL l)) : maxUnramifiedOutside F Ω S) : Ω) :=
  rfl

theorem mem_mackeySubgroup_gs_iff (v : S) (x : galUnramifiedOutside F Ω S)
    (σ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) /
      (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :
    σ ∈ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
        (gsFinFamily S ιs v).toMonoidHom x ↔
      ∀ l : L, σ (gsLocalEmbedding hL ιs v x l) = gsLocalEmbedding hL ιs v x l := by
  rw [mem_mackeySubgroup]
  change _ ∈ gsOpenSubgroup S hL ↔ _
  rw [mem_gsOpenSubgroup_iff]
  refine forall_congr' fun l => ?_
  have key := gsFinFamily_apply S ιs v σ ((x⁻¹ : galUnramifiedOutside F Ω S) (gsEmbedding hL l))
  rw [gsLocalEmbedding_apply, ← key]
  change x (gsFinFamily S ιs v σ (x⁻¹ (gsEmbedding hL l))) = gsEmbedding hL l ↔ _
  constructor
  · intro h
    have h' := congrArg (⇑(x⁻¹ : galUnramifiedOutside F Ω S)) h
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h'
    rw [h']
  · intro h
    have h' := Subtype.ext ((ιs v).injective h)
    rw [h', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem mackeySubgroup_gs_eq (v : S) (x : galUnramifiedOutside F Ω S) :
    mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
        (gsFinFamily S ιs v).toMonoidHom x = fixingOfAlgHom (gsLocalEmbedding hL ιs v x) :=
  Subgroup.ext fun σ => mem_mackeySubgroup_gs_iff hL ιs v x σ

theorem gsLocalEmbedding_mul (v : S) (x : galUnramifiedOutside F Ω S) {u : galUnramifiedOutside F Ω S}
    (hu : u ∈ gsOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) /
      (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) (l : L) :
    gsLocalEmbedding hL ιs v (u * x * gsFinFamily S ιs v h) l = h⁻¹ (gsLocalEmbedding hL ιs v x l) := by
  have hul := (mem_gsOpenSubgroup_iff S hL u).1 hu l
  have hu' : u⁻¹ (gsEmbedding hL l) = gsEmbedding hL l := by
    rw [AlgEquiv.aut_inv]
    exact u.symm_apply_eq.2 hul.symm
  rw [gsLocalEmbedding_apply, gsLocalEmbedding_apply, mul_inv_rev, mul_inv_rev, ← map_inv,
    AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu']
  exact gsFinFamily_apply S ιs v h⁻¹ _

theorem exists_gsLocalEmbedding_eq (v : S)
    (j : L →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :
    ∃ x, gsLocalEmbedding hL ιs v x = j := by
  let _ : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  have : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  let _ : Algebra L (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :=
    j.toRingHom.toAlgebra
  have : IsScalarTower F L (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  have : Algebra.IsAlgebraic L (maxUnramifiedOutside F Ω S) :=
    Algebra.IsAlgebraic.tower_top (K := F) L
  let j' : maxUnramifiedOutside F Ω S →ₐ[L]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) := IsAlgClosed.lift
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ((ιs v).comp (maxUnramifiedOutside F Ω S).val)
    (j'.restrictScalars F)
  refine ⟨g⁻¹, AlgHom.ext fun l => ?_⟩
  have h1 : j l = j' (gsEmbedding hL l) := (j'.commutes l).symm
  have h2 := DFunLike.congr_fun hg (gsEmbedding hL l)
  rw [h1, gsLocalEmbedding_apply, inv_inv]
  exact h2.symm

abbrev gsLocalPlace (v : S) (x : galUnramifiedOutside F Ω S) :
    PlacesOver L (v : HeightOneSpectrum (𝓞 F)) :=
  placeOfAlgHom (gsLocalEmbedding hL ιs v x)

theorem gsLocalPlace_mul (v : S) (x : galUnramifiedOutside F Ω S) {u : galUnramifiedOutside F Ω S}
    (hu : u ∈ gsOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) /
      (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :
    gsLocalPlace hL ιs v (u * x * gsFinFamily S ιs v h) = gsLocalPlace hL ιs v x := by
  have e : gsLocalEmbedding hL ιs v (u * x * gsFinFamily S ιs v h) =
      (((h⁻¹ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) /
        (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) →ₐ[(v : HeightOneSpectrum (𝓞 F)).adicCompletion F]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).restrictScalars F).comp
        (gsLocalEmbedding hL ιs v x) :=
    AlgHom.ext fun l => gsLocalEmbedding_mul hL ιs v x hu h l
  rw [gsLocalPlace, e, placeOfAlgHom_comp]

variable (S) in

def mackeyPlace (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs)) :
    (placesOver S : Set (HeightOneSpectrum (𝓞 L))) :=
  ⟨(gsLocalPlace hL ιs p.1 p.2.out).1, p.1.1, p.1.2, (gsLocalPlace hL ιs p.1 p.2.out).2⟩

theorem mackeyPlace_injective : Function.Injective (mackeyPlace S hL ιs) := by
  rintro ⟨v, d⟩ ⟨v', d'⟩ h
  have h1 : (gsLocalPlace hL ιs v d.out).1 = (gsLocalPlace hL ιs v' d'.out).1 := congrArg Subtype.val h
  have hv : v = v' := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    have a := (gsLocalPlace hL ιs v d.out).2
    have b := (gsLocalPlace hL ιs v' d'.out).2
    rw [h1] at a
    exact a.over.trans b.over.symm
  subst hv
  have h2 : gsLocalPlace hL ιs v d.out = gsLocalPlace hL ιs v d'.out := Subtype.ext h1
  obtain ⟨g, hg⟩ := exists_algEquiv_of_placeOfAlgHom_eq _ _ h2
  have hmem : d'.out * gsFinFamily S ιs v g * d.out⁻¹ ∈ gsOpenSubgroup S hL := by
    rw [mem_gsOpenSubgroup_iff]
    intro l
    have hinj : d'.out⁻¹ (gsEmbedding hL l) = gsFinFamily S ιs v g (d.out⁻¹ (gsEmbedding hL l)) :=
      Subtype.ext ((ιs v).injective ((hg l).trans (gsFinFamily_apply S ιs v g _).symm))
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hinj, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]
  have hd : d = d' := by
    rw [← DoubleCoset.out_eq' _ _ d, ← DoubleCoset.out_eq' _ _ d', DoubleCoset.eq]
    refine ⟨_, hmem, gsFinFamily S ιs v g⁻¹, ⟨g⁻¹, rfl⟩, ?_⟩
    rw [map_inv]
    group
  rw [hd]

theorem mackeyPlace_surjective : Function.Surjective (mackeyPlace S hL ιs) := by
  rintro ⟨w, v0, hv0, hw⟩
  let v : S := ⟨v0, hv0⟩
  obtain ⟨j, hj⟩ := exists_placeOfAlgHom_eq (⟨w, hw⟩ : PlacesOver L v0)
  obtain ⟨x, hx⟩ := exists_gsLocalEmbedding_eq hL ιs v j
  let d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
      (gsFinFamily S ιs v).toMonoidHom :=
    DoubleCoset.mk _ _ x
  refine ⟨⟨v, d⟩, ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) (gsFinFamily S ιs v).toMonoidHom.range x
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hb
  apply Subtype.ext
  change (gsLocalPlace hL ιs v d.out).1 = w
  have e1 : d.out = a * x * gsFinFamily S ιs v h := hab
  rw [e1, gsLocalPlace_mul hL ιs v x ha h, gsLocalPlace, hx, hj]

variable (S) in

def mackeyPlaceEquiv :
    MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs) ≃ (placesOver S : Set (HeightOneSpectrum (𝓞 L))) :=
  Equiv.ofBijective (mackeyPlace S hL ιs) ⟨mackeyPlace_injective hL ιs, mackeyPlace_surjective hL ιs⟩

theorem coe_mackeyPlaceEquiv (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs)) :
    (mackeyPlaceEquiv S hL ιs p : HeightOneSpectrum (𝓞 L)) = (gsLocalPlace hL ιs p.1 p.2.out).1 :=
  rfl

omit [IsScalarTower F L Ω] in
variable (S) in

def gsAutLift (x : galUnramifiedOutside F Ω S) : Gal(Ω/F) :=
  (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside F Ω S) Ω x).choose

omit [IsScalarTower F L Ω] in
theorem gsAutLift_apply (x : galUnramifiedOutside F Ω S) (y : maxUnramifiedOutside F Ω S) :
    gsAutLift S x (y : Ω) = ((x y : maxUnramifiedOutside F Ω S) : Ω) := by
  have h := (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside F Ω S) Ω x).choose_spec
  conv_rhs => rw [← h]
  exact (AlgEquiv.restrictNormal_commutes (gsAutLift S x) (maxUnramifiedOutside F Ω S) y).symm

omit [IsScalarTower F L Ω] in
theorem gsAutLift_inv_apply (x : galUnramifiedOutside F Ω S) (y : maxUnramifiedOutside F Ω S) :
    (gsAutLift S x)⁻¹ (y : Ω) = (((x⁻¹ : galUnramifiedOutside F Ω S) y : maxUnramifiedOutside F Ω S) : Ω) := by
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, gsAutLift_apply, ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

def gsLocalEmbeddingOver (v : S) (x : galUnramifiedOutside F Ω S) :
    Ω →ₐ[L] AlgebraicClosure ((gsLocalPlace hL ιs v x).1.adicCompletion L) :=
  { ((closureEquivOfAlgHom (gsLocalEmbedding hL ιs v x)).toRingHom.comp
      ((ιs v).toRingHom.comp ((gsAutLift S x)⁻¹ : Gal(Ω/F)).toRingEquiv.toRingHom)) with
    commutes' := fun l => by
      change closureEquivOfAlgHom (gsLocalEmbedding hL ιs v x)
        (ιs v ((gsAutLift S x)⁻¹ (((gsEmbedding hL l : maxUnramifiedOutside F Ω S)) : Ω))) = _
      rw [gsAutLift_inv_apply]
      change closureEquivOfAlgHom (gsLocalEmbedding hL ιs v x) (gsLocalEmbedding hL ιs v x l) = _
      rw [← completionEmbeddingOfAlgHom_algebraMap, closureEquivOfAlgHom_completionEmbedding]
      exact (IsScalarTower.algebraMap_apply L ((gsLocalPlace hL ιs v x).1.adicCompletion L) _ l).symm }

theorem gsLocalEmbeddingOver_apply (v : S) (x : galUnramifiedOutside F Ω S) (y : Ω) :
    gsLocalEmbeddingOver hL ιs v x y =
      closureEquivOfAlgHom (gsLocalEmbedding hL ιs v x) (ιs v ((gsAutLift S x)⁻¹ y)) :=
  rfl

def gsMackeyLocalEquiv (v : S) (x : galUnramifiedOutside F Ω S) :
    mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
        (gsFinFamily S ιs v).toMonoidHom x ≃ₜ*
      Gal(AlgebraicClosure ((gsLocalPlace hL ιs v x).1.adicCompletion L) /
        (gsLocalPlace hL ιs v x).1.adicCompletion L) :=
  (continuousMulEquivOfSubgroupEq (mackeySubgroup_gs_eq hL ιs v x)).trans
    (fixingOfAlgHomEquiv (gsLocalEmbedding hL ιs v x))

theorem gsMackeyLocalEquiv_apply (v : S) (x : galUnramifiedOutside F Ω S)
    (σ : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
      (gsFinFamily S ιs v).toMonoidHom x)
    (z : AlgebraicClosure ((gsLocalPlace hL ιs v x).1.adicCompletion L)) :
    gsMackeyLocalEquiv hL ιs v x σ z = closureEquivOfAlgHom (gsLocalEmbedding hL ιs v x)
      (σ.1 ((closureEquivOfAlgHom (gsLocalEmbedding hL ιs v x)).symm z)) :=
  rfl

variable [IsGalois L Ω]

theorem gsBaseChange_mackeyConj (v : S) (x : galUnramifiedOutside F Ω S)
    (σ : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
      (gsFinFamily S ιs v).toMonoidHom x) :
    gsBaseChange S hL (mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
        (gsFinFamily S ιs v).toMonoidHom x σ) =
      decompHomS ((gsLocalPlace hL ιs v x).1.adicCompletion L) (placesOver S)
        (gsLocalEmbeddingOver hL ιs v x) (gsMackeyLocalEquiv hL ιs v x σ) := by
  symm
  rw [decompHomS, decompHom_eq_iff]
  intro t
  have hu := coe_gsBaseChange_apply hL (mackeyConj (gsOpenSubgroup S hL :
    Subgroup (galUnramifiedOutside F Ω S)) (gsFinFamily S ιs v).toMonoidHom x σ) t
  have ht : ((t : maxUnramifiedOutside L Ω (placesOver S)) : Ω) =
      (((gsFieldEquiv hL).symm t : maxUnramifiedOutside F Ω S) : Ω) :=
    (coe_fieldEquivOfRestrictScalarsEq_symm (restrictScalars_maxUnramifiedOutside_eq S hL) t).symm
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IntermediateField.coe_val, gsLocalEmbeddingOver_apply,
    gsLocalEmbeddingOver_apply, gsMackeyLocalEquiv_apply, RingEquiv.symm_apply_apply, hu, ht,
    mackeyConj_apply_coe]
  have key : (gsAutLift S x)⁻¹ ((((x * (gsFinFamily S ιs v).toMonoidHom σ * x⁻¹)
      ((gsFieldEquiv hL).symm t) : maxUnramifiedOutside F Ω S)) : Ω) =
      ((gsFinFamily S ιs v σ ((x⁻¹ : galUnramifiedOutside F Ω S) ((gsFieldEquiv hL).symm t)) :
        maxUnramifiedOutside F Ω S) : Ω) := by
    rw [gsAutLift_inv_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply x⁻¹ x,
      inv_mul_cancel, AlgEquiv.one_apply]
    rfl
  rw [key, gsFinFamily_apply, gsAutLift_inv_apply]

theorem gsBaseChange_mackeyFamily (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (σ : mackeyGroup (gsOpenSubgroup S hL) (gsFinFamily S ιs) p) :
    gsBaseChange S hL (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs) p σ) =
      decompHomS ((gsLocalPlace hL ιs p.1 p.2.out).1.adicCompletion L) (placesOver S)
        (gsLocalEmbeddingOver hL ιs p.1 p.2.out) (gsMackeyLocalEquiv hL ιs p.1 p.2.out σ) :=
  gsBaseChange_mackeyConj hL ιs p.1 p.2.out σ

end Mackey

end

end GroundTheory.ProfCoh
