import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal GroundTheory.Global.IdeleGroup

open scoped Pointwise NumberField.LiesOver NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

set_option synthInstance.maxHeartbeats 200000

variable {K F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v)

theorem finiteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
    (x : IdeleGroup F.1) :
    finiteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • finiteProj w.1 x := by
  apply Units.ext
  have h : w.1 = (σ : F.1 ≃ₐ[K.1] F.1) • w.1 :=
    (congrArg Subtype.val ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2)).symm
  rw [coe_finiteProj, coe_smul_idele, smul_snd_eq_galHom _ _ w.1 w.1 h, galHom_eq_decomposition]
  rfl

def finiteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (finiteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (finiteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def finiteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype
    continuous_of_discreteTopology (finiteComponentRep w) n

set_option maxHeartbeats 2000000 in

theorem placeProj_comp_finiteShapiroIso (n : ℕ) :
    cohomologyMap (finiteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (finiteShapiroIso v w n).hom =
      finiteComponent w n := by
  change HomologicalComplex.homologyMap (cochainsMap (finiteProjAboveRep (K := K.1) (L := F.1) v)) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong _ (continuous_subgroup_subtype _)
        (orbitProj (permutesFactors_finiteUnitsAboveRep v)
          (mem_stabilizer_iff_smul_eq v w))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (stabRepFiniteIso v w).hom) n) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in

theorem ideleEmbedding_snd_of_below_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : HeightOneSpectrum (𝓞 E.1)) (u : HeightOneSpectrum (𝓞 F.1)) (hu : below F.1 w' = u)
    [w'.asIdeal.LiesOver u.asIdeal] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).2 w' =
      SemiLocal.completionMap u w' ((x : 𝔸[F.1]).2 u) := by
  subst hu
  rfl

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 2000000 in

theorem levelTransition_comp_finiteComponent (w' : PlacesOver E.1 v)
    [w'.1.asIdeal.LiesOver w.1.asIdeal] (n : ℕ) :
    levelTransition K F E n ≫ finiteComponent w' n =
      finiteComponent w n ≫ localTransition K F E w w' n := by
  unfold levelTransition finiteComponent localTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change ((ideleEmbedding F.1 E.1 _ : IdeleGroup E.1) : 𝔸[E.1]).2 w'.1 =
    SemiLocal.completionMap w.1 w'.1 _
  exact ideleEmbedding_snd_of_below_eq w'.1 w.1 ((below_eq_iff w'.1 w.1).2 inferInstance) _

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1)

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem fst_eq_completionCongr (a : 𝔸[F.1]) {u u' : InfinitePlace F.1} (h : u = u') :
    a.1 u' = completionCongr h (a.1 u) := by
  subst h
  rfl

omit [F.1.fixingSubgroup.Normal] in
theorem eq_comap_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
    w.1 = w.1.comap (((σ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) : F.1 →+* F.1) := by
  rw [comap_eq_inv_smul]
  exact (MulAction.mem_stabilizer_iff.1 (inv_mem σ.2)).symm

theorem infiniteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
    (x : IdeleGroup F.1) :
    infiniteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • infiniteProj w.1 x := by
  apply Units.ext
  rw [coe_infiniteProj, coe_smul_idele, smul_fst,
    fst_eq_completionCongr _ (eq_comap_of_mem_stabilizer w σ), infiniteCompletionMap_eq_decomposition]
  rfl

def infiniteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (infiniteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (infiniteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def infiniteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype
    continuous_of_discreteTopology (infiniteComponentRep w) n

set_option maxHeartbeats 2000000 in

theorem placeProj_comp_infiniteShapiroIso (n : ℕ) :
    cohomologyMap (infiniteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (infiniteShapiroIso v w n).hom =
      infiniteComponent w n := by
  change HomologicalComplex.homologyMap (cochainsMap (infiniteProjAboveRep (K := K.1) (L := F.1) v)) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong _ (continuous_subgroup_subtype _)
        (orbitProj (permutesFactors_infiniteUnitsAboveRep v)
          (mem_stabilizer_iff_smul_eq_infinite v w))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (stabRepInfiniteIso v w).hom) n) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in

theorem ideleEmbedding_fst_of_comap_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : InfinitePlace E.1) (u : InfinitePlace F.1) (hu : w'.comap (algebraMap F.1 E.1) = u)
    [w'.LiesOver u] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).1 w' =
      NumberField.LiesOver.completionMap (v := u) (w := w') ((x : 𝔸[F.1]).1 u) := by
  subst hu
  rfl

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 2000000 in

theorem levelTransition_comp_infiniteComponent (w' : v.placesOver E.1) [w'.1.LiesOver w.1] (n : ℕ) :
    levelTransition K F E n ≫ infiniteComponent w' n =
      infiniteComponent w n ≫ infLocalTransition K F E w w' n := by
  unfold levelTransition infiniteComponent infLocalTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change ((ideleEmbedding F.1 E.1 _ : IdeleGroup E.1) : 𝔸[E.1]).1 w'.1 =
    NumberField.LiesOver.completionMap (v := w.1) (w := w'.1) _
  exact ideleEmbedding_fst_of_comap_eq w'.1 w.1 (InfinitePlace.LiesOver.comap_eq w'.1 w.1) _

end Infinite

end

end GroundTheory.ProfCoh
