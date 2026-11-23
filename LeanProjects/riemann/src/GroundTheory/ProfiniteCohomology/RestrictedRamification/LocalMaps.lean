import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section DecompHom

variable {K E Kv Ωv : Type u} [Field K] [Field E] [Field Kv] [Field Ωv] [Algebra K E]
  [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]

variable (Kv) in

noncomputable def decompHom [Normal K E] (ι : E →ₐ[K] Ωv) : Gal(Ωv/Kv) →* Gal(E/K) :=
  letI : Algebra E Ωv := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K)

theorem decompHom_apply [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (x : E) :
    ι (decompHom Kv ι σ x) = σ (ι x) := by
  let _ : Algebra E Ωv := ι.toRingHom.toAlgebra
  have : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E x

theorem decompHom_eq_iff [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (τ : Gal(E/K)) :
    decompHom Kv ι σ = τ ↔ ∀ x, ι (τ x) = σ (ι x) := by
  constructor
  · rintro rfl x
    exact decompHom_apply ι σ x
  · intro h
    ext x
    apply ι.injective
    change ι _ = ι _
    rw [decompHom_apply, h]

theorem continuous_decompHom [Normal K E] (ι : E →ₐ[K] Ωv) : Continuous (decompHom Kv ι) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨L, hL, hLU⟩ := hU
  let b := Module.finBasis K L
  let T : IntermediateField Kv Ωv := IntermediateField.adjoin Kv (Set.range fun i => ι (b i))
  have hT : FiniteDimensional Kv T := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((Algebra.IsAlgebraic.isAlgebraic (R := K) ((b i : L) : E)).isIntegral.map ι).tower_top
  apply mem_nhds_iff.mpr
  refine ⟨T.fixingSubgroup, fun σ hσ => hLU ?_, T.fixingSubgroup_isOpen, one_mem _⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, decompHom Kv ι σ (b i : E) = b i := fun i => by
    apply ι.injective
    change ι _ = ι _
    rw [decompHom_apply]
    exact hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  intro y hy
  have hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E) := by
    have := congrArg L.val (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hy', map_sum]
  simp only [map_smul, hb]

theorem exists_eq_comp_of_normal [Normal K E] (ι ι' : E →ₐ[K] Ωv) :
    ∃ g : Gal(E/K), ι' = ι.comp (g : E →ₐ[K] E) := by
  let _ : Algebra E Ωv := ι.toRingHom.toAlgebra
  have : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨ι'.restrictNormal' E, ?_⟩
  ext x
  exact (AlgHom.restrictNormal_commutes ι' E x).symm

theorem decompHom_comp [Normal K E] (ι : E →ₐ[K] Ωv) (g : Gal(E/K)) (σ : Gal(Ωv/Kv)) :
    decompHom Kv (ι.comp (g : E →ₐ[K] E)) σ = g⁻¹ * decompHom Kv ι σ * g := by
  rw [decompHom_eq_iff]
  intro x
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
    AlgEquiv.apply_symm_apply, decompHom_apply]

theorem decompHom_comp_val [Normal K E] (ι : E →ₐ[K] Ωv) (N : IntermediateField K E) [Normal K N] :
    decompHom Kv (ι.comp N.val) = (AlgEquiv.restrictNormalHom N).comp (decompHom Kv ι) := by
  ext σ x
  apply ι.injective
  change (ι.comp N.val) (decompHom Kv (ι.comp N.val) σ x) =
    ι ((AlgEquiv.restrictNormalHom N (decompHom Kv ι σ) x : N) : E)
  rw [decompHom_apply, AlgEquiv.restrictNormalHom_apply, decompHom_apply]
  rfl

theorem nonempty_algHom_of_isSepClosed [Algebra.IsSeparable K E] [IsSepClosed Ωv] :
    Nonempty (E →ₐ[K] Ωv) :=
  ⟨IsSepClosed.lift⟩

end DecompHom

section Conj

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] [CompactSpace G]

noncomputable def conjResMor (A : Rep.{u} k G) {φ φ' : H →* G} (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) : Rep.res φ A ⟶ Rep.res φ' A :=
  Rep.ofHom ⟨A.ρ g⁻¹, fun x => by
    ext a
    change A.ρ g⁻¹ (A.ρ (φ x) a) = A.ρ (φ' x) (A.ρ g⁻¹ a)
    rw [h, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] in
theorem conjResMor_hom_apply (A : Rep.{u} k G) {φ φ' : H →* G} (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) (a : A) : (conjResMor A g h).hom a = A.ρ g⁻¹ a :=
  rfl

theorem cohomologyMapAlong_conj (A : Rep.{u} k G) [IsDiscreteRep A] {φ φ' : H →* G}
    (hφ : Continuous φ) (hφ' : Continuous φ') (g : G) (h : ∀ x, φ' x = g⁻¹ * φ x * g)
    [IsDiscreteRep (Rep.res φ A)] [IsDiscreteRep (Rep.res φ' A)] (n : ℕ) :
    cohomologyMapAlong φ' hφ' (𝟙 _) n =
      cohomologyMapAlong φ hφ (𝟙 _) n ≫
        cohomologyMapAlong (MonoidHom.id H) continuous_id (conjResMor A g h) n := by
  have hφ'eq : φ' = (innerConjHom g).comp φ := MonoidHom.ext fun x => h x
  subst hφ'eq
  have e1 : (𝟙 (Rep.res ((innerConjHom g).comp φ) A)) =
      (Rep.resFunctor φ).map (innerConjMor A g) ≫ conjResMor A g h := by
    ext a
    change a = A.ρ g⁻¹ (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : conjResMor A g h =
      (Rep.resFunctor (MonoidHom.id H)).map (𝟙 (Rep.res φ A)) ≫ conjResMor A g h := by
    ext a
    rfl
  calc cohomologyMapAlong ((innerConjHom g).comp φ) hφ' (𝟙 _) n
      = cohomologyMapAlong ((innerConjHom g).comp φ) ((continuous_innerConjHom g).comp hφ)
          ((Rep.resFunctor φ).map (innerConjMor A g) ≫ conjResMor A g h) n := by rw [← e1]
    _ = cohomologyInnerConj A n g ≫ cohomologyMapAlong φ hφ (conjResMor A g h) n :=
        cohomologyMapAlong_comp _ _ _ _ _ _ _
    _ = cohomologyMapAlong φ hφ (conjResMor A g h) n := by
        rw [cohomologyInnerConj_eq_id, Category.id_comp]
    _ = cohomologyMapAlong (φ.comp (MonoidHom.id H)) (hφ.comp continuous_id)
          ((Rep.resFunctor (MonoidHom.id H)).map (𝟙 (Rep.res φ A)) ≫ conjResMor A g h) n := by
        rw [← e2]
        rfl
    _ = cohomologyMapAlong φ hφ (𝟙 _) n ≫
          cohomologyMapAlong (MonoidHom.id H) continuous_id (conjResMor A g h) n :=
        cohomologyMapAlong_comp _ _ _ _ _ _ _

end Conj

section Local

variable {k K E Kv Ωv : Type u} [CommRing k] [Field K] [Field E] [Field Kv] [Field Ωv]
  [Algebra K E] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]
  [IsGalois K E]

instance isDiscreteRep_res_decompHom (ι : E →ₐ[K] Ωv) (A : Rep.{u} k Gal(E/K)) [IsDiscreteRep A] :
    IsDiscreteRep (Rep.res (decompHom Kv ι) A) :=
  IsDiscreteRep.res (continuous_decompHom ι) A

variable (Kv) in

noncomputable def localCohomologyMap (ι : E →ₐ[K] Ωv) (A : Rep.{u} k Gal(E/K)) [IsDiscreteRep A]
    (n : ℕ) : cohomology A n ⟶ cohomology (Rep.res (decompHom Kv ι) A) n :=
  cohomologyMapAlong (decompHom Kv ι) (continuous_decompHom ι) (𝟙 _) n

theorem localCohomologyMap_comp (ι : E →ₐ[K] Ωv) (g : Gal(E/K)) (A : Rep.{u} k Gal(E/K))
    [IsDiscreteRep A] (n : ℕ) :
    localCohomologyMap Kv (ι.comp (g : E →ₐ[K] E)) A n =
      localCohomologyMap Kv ι A n ≫
        cohomologyMapAlong (MonoidHom.id _) continuous_id
          (conjResMor (φ := decompHom Kv ι) (φ' := decompHom Kv (ι.comp (g : E →ₐ[K] E))) A g
            (decompHom_comp ι g)) n :=
  cohomologyMapAlong_conj A (continuous_decompHom ι) (continuous_decompHom _) g
    (decompHom_comp ι g) n

end Local

section Places

open NumberField IsDedekindDomain

variable {K Ω Kv Ωv : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [Field Kv] [Field Ωv] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]

variable (Kv) in

noncomputable def decompHomS (S : Set (HeightOneSpectrum (𝓞 K))) (ι : Ω →ₐ[K] Ωv) :
    Gal(Ωv/Kv) →* galUnramifiedOutside K Ω S :=
  decompHom Kv (ι.comp (maxUnramifiedOutside K Ω S).val)

theorem decompHomS_eq (S : Set (HeightOneSpectrum (𝓞 K))) (ι : Ω →ₐ[K] Ωv) :
    decompHomS Kv S ι =
      (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)).comp (decompHom Kv ι) :=
  decompHom_comp_val ι _

theorem continuous_decompHomS (S : Set (HeightOneSpectrum (𝓞 K))) (ι : Ω →ₐ[K] Ωv) :
    Continuous (decompHomS Kv S ι) :=
  continuous_decompHom _

omit [IsGalois K Ω] in

theorem nonempty_algHom_adicCompletion [IsSepClosure K Ω] (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K)) :=
  nonempty_algHom_of_isSepClosed

omit [NumberField K] [IsGalois K Ω] in

theorem nonempty_algHom_infinitePlace_completion [IsSepClosure K Ω] (v : InfinitePlace K) :
    Nonempty (Ω →ₐ[K] AlgebraicClosure v.Completion) :=
  nonempty_algHom_of_isSepClosed

end Places

end GroundTheory.ProfCoh
