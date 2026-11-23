import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.UnitsLevels
import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section General

variable (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv] [Algebra K.1 Ωv]
  [IsScalarTower K.1 Kv Ωv] [Algebra.IsIntegral Kv Ωv] (ι : ℚ̄ →ₐ[K.1] Ωv)

def globalDecomp : Gal(Ωv/Kv) →* K.1.fixingSubgroup :=
  ((AlgEquiv.restrictScalarsHom ℚ).comp (decompHom Kv ι)).codRestrict _ fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (decompHom Kv ι σ).commutes ⟨x, hx⟩

omit [Algebra.IsIntegral Kv Ωv] in

theorem globalDecomp_apply (σ : Gal(Ωv/Kv)) (x : ℚ̄) :
    ι ((globalDecomp Kv ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) x) = σ (ι x) :=
  decompHom_apply ι σ x

omit [Algebra.IsIntegral Kv Ωv] in
theorem continuous_globalDecomp : Continuous (globalDecomp Kv ι) :=
  ((continuous_restrictScalarsHom_of_tower ℚ K.1 ℚ̄).comp (continuous_decompHom ι)).subtype_mk _

theorem decompHom_eq_restrictHom_globalDecomp (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]
    (j : F.1 →ₐ[K.1] Ωv) (hj : ∀ x : F.1, j x = ι x) (σ : Gal(Ωv/Kv)) :
    decompHom Kv j σ = restrictHom (E := F) (globalDecomp Kv ι σ) :=
  (decompHom_eq_iff j σ _).2 fun x => by
    rw [hj, hj, coe_restrictHom_apply, globalDecomp_apply]

def unitsLocalMor : Rep.res (globalDecomp Kv ι) (unitsLimitRep K) ⟶ galUnitsZ Kv Ωv :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map ι.toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ => LinearMap.ext fun _ => congrArg Additive.ofMul (Units.ext (globalDecomp_apply Kv ι σ _))⟩

@[simp]
theorem unitsLocalMor_hom_apply (x : Additive ℚ̄ˣ) :
    ((Additive.toMul ((unitsLocalMor Kv ι).hom x) : Ωvˣ) : Ωv) = ι (x.toMul : ℚ̄) :=
  rfl

def unitsLocalRes (n : ℕ) : cohomology (unitsLimitRep K) n ⟶ cohomology (galUnitsZ Kv Ωv) n :=
  cohomologyMapAlong (globalDecomp Kv ι) (continuous_globalDecomp Kv ι) (unitsLocalMor Kv ι) n

end General

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem coe_localDecompHom_eq_restrictHom (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    ((localDecompHom ι F σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) (placeOfEmbedding ι F).1.asIdeal) :
      F.1 ≃ₐ[K.1] F.1) = restrictHom (E := F) (globalDecomp (v.adicCompletion K.1) ι σ) :=
  decompHom_eq_restrictHom_globalDecomp _ ι F (embedLevel ι F) (embedLevel_apply ι F) σ

theorem localUnitsMor_finiteComponentRep_levelDiag (u : Additive F.1ˣ) :
    (localUnitsMor ι F).hom ((finiteComponentRep (placeOfEmbedding ι F)).hom ((levelDiag K F).hom u)) =
      (unitsLocalMor (v.adicCompletion K.1) ι).hom ((unitsLevelMor K F).hom u) :=
  congrArg Additive.ofMul (Units.ext (completionEmbedding_algebraMap ι F (u.toMul : F.1)))

set_option maxHeartbeats 4000000 in

theorem localInfl_finiteComponent_levelDiag (n : ℕ) (y : cohomology (galUnitsZ K.1 F.1) n) :
    (localInfl ι F n).hom ((finiteComponent (placeOfEmbedding ι F) n).hom
      ((cohomologyMap (levelDiag K F) n).hom y)) =
      (unitsLocalRes (v.adicCompletion K.1) ι n).hom ((unitsLevelInfl K F n).hom y) := by
  have h : cohomologyMap (levelDiag K F) n ≫ finiteComponent (placeOfEmbedding ι F) n ≫ localInfl ι F n =
      unitsLevelInfl K F n ≫ unitsLocalRes (v.adicCompletion K.1) ι n := by
    rw [← cohomologyMapAlong_id_eq_cohomologyMap, finiteComponent, localInfl, unitsLevelInfl, unitsLocalRes,
      ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _
      (MonoidHom.ext fun σ => coe_localDecompHom_eq_restrictHom ι F σ)
      (fun u => localUnitsMor_finiteComponentRep_levelDiag ι F u) n
  exact congrArg (fun φ => φ.hom y) h

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
  (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem levelDiag_infiniteComponent_infLocalInfl_cochains :
    cochainsMap (levelDiag K F) ≫
      cochainsMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1)
          (infPlaceOfEmbedding ι F : InfinitePlace F.1)).subtype
        continuous_of_discreteTopology (infiniteComponentRep (infPlaceOfEmbedding ι F)) ≫
      cochainsMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F) (infLocalUnitsMor ι F) =
    cochainsMapAlong restrictHom continuous_restrictHom (unitsLevelMor K F) ≫
      cochainsMapAlong (globalDecomp v.Completion ι) (continuous_globalDecomp _ ι)
        (unitsLocalMor v.Completion ι) := by
  have hfun : ∀ σ : Gal(AlgebraicClosure v.Completion/v.Completion),
      ((infLocalDecompHom ι F σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1)
        (infPlaceOfEmbedding ι F : InfinitePlace F.1)) : F.1 ≃ₐ[K.1] F.1) =
        restrictHom (E := F) (globalDecomp v.Completion ι σ) :=
    fun σ => decompHom_eq_restrictHom_globalDecomp _ ι F (infEmbedLevel ι F) (infEmbedLevel_apply ι F) σ
  have hval : ∀ u : Additive F.1ˣ,
      (infLocalUnitsMor ι F).hom ((infiniteComponentRep (infPlaceOfEmbedding ι F)).hom
        ((levelDiag K F).hom u)) = (unitsLocalMor v.Completion ι).hom ((unitsLevelMor K F).hom u) := fun u =>
    congrArg Additive.ofMul (Units.ext (infCompletionEmbedding_algebraMap ι F (u.toMul : F.1)))
  ext m c : 3
  apply Subtype.ext
  funext σ
  change (infLocalUnitsMor ι F).hom ((infiniteComponentRep (infPlaceOfEmbedding ι F)).hom ((levelDiag K F).hom
      (c.1 fun i => ((infLocalDecompHom ι F (σ i) : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1)
        (infPlaceOfEmbedding ι F : InfinitePlace F.1)) : F.1 ≃ₐ[K.1] F.1)))) =
    (unitsLocalMor v.Completion ι).hom ((unitsLevelMor K F).hom
      (c.1 fun i => restrictHom (E := F) (globalDecomp v.Completion ι (σ i))))
  rw [funext fun i => hfun (σ i)]
  exact hval _

set_option maxHeartbeats 4000000 in

theorem infLocalInfl_infiniteComponent_levelDiag (n : ℕ) (y : cohomology (galUnitsZ K.1 F.1) n) :
    (infLocalInfl ι F n).hom ((infiniteComponent (infPlaceOfEmbedding ι F) n).hom
      ((cohomologyMap (levelDiag K F) n).hom y)) =
      (unitsLocalRes v.Completion ι n).hom ((unitsLevelInfl K F n).hom y) := by
  have e1 : cohomologyMap (levelDiag K F) n ≫ infiniteComponent (infPlaceOfEmbedding ι F) n ≫
      infLocalInfl ι F n =
      HomologicalComplex.homologyMap (cochainsMap (levelDiag K F) ≫
        cochainsMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1)
            (infPlaceOfEmbedding ι F : InfinitePlace F.1)).subtype
          continuous_of_discreteTopology (infiniteComponentRep (infPlaceOfEmbedding ι F)) ≫
        cochainsMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F)
          (infLocalUnitsMor ι F)) n := by
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    rfl
  have e2 : unitsLevelInfl K F n ≫ unitsLocalRes v.Completion ι n =
      HomologicalComplex.homologyMap (cochainsMapAlong restrictHom continuous_restrictHom (unitsLevelMor K F) ≫
        cochainsMapAlong (globalDecomp v.Completion ι) (continuous_globalDecomp _ ι)
          (unitsLocalMor v.Completion ι)) n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm
  have h : cohomologyMap (levelDiag K F) n ≫ infiniteComponent (infPlaceOfEmbedding ι F) n ≫
      infLocalInfl ι F n = unitsLevelInfl K F n ≫ unitsLocalRes v.Completion ι n := by
    rw [e1, e2, levelDiag_infiniteComponent_infLocalInfl_cochains]
  exact congrArg (fun φ => φ.hom y) h

end Infinite

section Components

variable (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n)

set_option maxHeartbeats 4000000 in

theorem idelesLimitCohomologyEquiv_unitsToIdeles_inr (v : HeightOneSpectrum (𝓞 K.1))
    (x : cohomology (unitsLimitRep K) n) :
    idelesLimitCohomologyEquiv ι hn ((unitsToIdeles K n).hom x) (.inr v) =
      (unitsLocalRes (v.adicCompletion K.1) (ι.fin v) n).hom x := by
  obtain ⟨p, y, rfl⟩ := exists_unitsLevelInfl_eq n x
  rw [unitsToIdeles_unitsLevelInfl, idelesLimitCohomologyEquiv_levelInfl]
  change (localInfl (ι.fin v) p.1 n).hom (ι.places.shapiro n (.inr v) p
      ((cohomologyMap (placeProj (.inr v)) n).hom ((cohomologyMap (levelDiag K p.1) n).hom y))) = _
  rw [CompatiblePlaces.shapiro_placeProj_inr]
  exact localInfl_finiteComponent_levelDiag (ι.fin v) p.1 n y

set_option maxHeartbeats 4000000 in

theorem idelesLimitCohomologyEquiv_unitsToIdeles_inl (v : InfinitePlace K.1)
    (x : cohomology (unitsLimitRep K) n) :
    idelesLimitCohomologyEquiv ι hn ((unitsToIdeles K n).hom x) (.inl v) =
      (unitsLocalRes v.Completion (ι.inf v) n).hom x := by
  obtain ⟨p, y, rfl⟩ := exists_unitsLevelInfl_eq n x
  rw [unitsToIdeles_unitsLevelInfl, idelesLimitCohomologyEquiv_levelInfl]
  change (infLocalInfl (ι.inf v) p.1 n).hom (ι.places.shapiro n (.inl v) p
      ((cohomologyMap (placeProj (.inl v)) n).hom ((cohomologyMap (levelDiag K p.1) n).hom y))) = _
  rw [CompatiblePlaces.shapiro_placeProj_inl]
  exact infLocalInfl_infiniteComponent_levelDiag (ι.inf v) p.1 n y

theorem brauerLocal_apply_inr (v : HeightOneSpectrum (𝓞 K.1)) (x : cohomology (unitsLimitRep K) 2) :
    brauerLocal ι x (.inr v) = (unitsLocalRes (v.adicCompletion K.1) (ι.fin v) 2).hom x :=
  idelesLimitCohomologyEquiv_unitsToIdeles_inr ι _ v x

theorem brauerLocal_apply_inl (v : InfinitePlace K.1) (x : cohomology (unitsLimitRep K) 2) :
    brauerLocal ι x (.inl v) = (unitsLocalRes v.Completion (ι.inf v) 2).hom x :=
  idelesLimitCohomologyEquiv_unitsToIdeles_inl ι _ v x

end Components

end

end GroundTheory.ProfCoh
