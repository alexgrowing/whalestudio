import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.LiesOver
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfLiesOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

def joinField (K F : FiniteSubfield) : FiniteSubfield := ⟨K.1 ⊔ F.1, inferInstance⟩

theorem le_joinField_left (K F : FiniteSubfield) : K ≤ joinField K F :=
  (le_sup_left : K.1 ≤ K.1 ⊔ F.1)

theorem le_joinField_right (K F : FiniteSubfield) : F ≤ joinField K F :=
  (le_sup_right : F.1 ≤ K.1 ⊔ F.1)

instance fact_le_joinField (K F : FiniteSubfield) : Fact (K ≤ joinField K F) := ⟨le_joinField_left K F⟩

theorem joinField_mono (K : FiniteSubfield) {F E : FiniteSubfield} (h : F ≤ E) : joinField K F ≤ joinField K E :=
  sup_le_sup_left (show F.1 ≤ E.1 from h) K.1

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

def idelesLevelProj (F : FiniteSubfield) [Fact (K ≤ F)] :
    IdeleGroup F.1 →* (AlgebraicClosure (v.adicCompletion K.1))ˣ :=
  (Units.map (completionEmbedding ι F).toRingHom.toMonoidHom).comp (finiteProj (placeOfEmbedding ι F).1)

theorem coe_idelesLevelProj (F : FiniteSubfield) [Fact (K ≤ F)] (x : IdeleGroup F.1) :
    ((idelesLevelProj ι F x : (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)) =
      completionEmbedding ι F ((x : 𝔸[F.1]).2 (placeOfEmbedding ι F).1) :=
  rfl

theorem idelesLevelProj_ideleMap {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] (h : F ≤ E)
    (x : IdeleGroup F.1) : idelesLevelProj ι E (ideleMap h x) = idelesLevelProj ι F x := by
  have : Fact (F ≤ E) := ⟨h⟩
  apply Units.ext
  rw [coe_idelesLevelProj, coe_idelesLevelProj, ← completionEmbedding_completionMap ι (F := F) (E := E)]
  congr 1
  exact ideleEmbedding_snd_of_below_eq (placeOfEmbedding ι E).1 (placeOfEmbedding ι F).1
    ((AdeleBaseChange.below_eq_iff _ _).2 inferInstance) x

def idelesProj : IdeleLimit →* (AlgebraicClosure (v.adicCompletion K.1))ˣ :=
  IdeleLimit.lift (fun F => (idelesLevelProj ι (joinField K F)).comp (ideleMap (le_joinField_right K F)))
    fun F E h x => by
      change idelesLevelProj ι (joinField K E) (ideleMap _ (ideleMap h x)) =
        idelesLevelProj ι (joinField K F) (ideleMap _ x)
      rw [ideleMap_ideleMap, ← idelesLevelProj_ideleMap ι (joinField_mono K h), ideleMap_ideleMap]

theorem idelesProj_of (F : FiniteSubfield) [Fact (K ≤ F)] (x : IdeleGroup F.1) :
    idelesProj ι (of F x) = idelesLevelProj ι F x :=
  idelesLevelProj_ideleMap ι (le_joinField_right K F) x

theorem coe_idelesProj_of (F : FiniteSubfield) [Fact (K ≤ F)] (x : IdeleGroup F.1) :
    ((idelesProj ι (of F x) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)) =
      completionEmbedding ι F ((x : 𝔸[F.1]).2 (placeOfEmbedding ι F).1) := by
  rw [idelesProj_of, coe_idelesLevelProj]

set_option maxHeartbeats 2000000 in

theorem idelesProj_smul (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) (z : IdeleLimit) :
    idelesProj ι ((globalDecomp (v.adicCompletion K.1) ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) • z) = σ • idelesProj ι z := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) F
  rw [← of_ideleMap hp x]
  generalize ideleMap hp x = y
  rw [smul_of_restrictHom, ← coe_localDecompHom_eq_restrictHom ι p.1 σ]
  apply Units.ext
  change _ = σ ((idelesProj ι (of p.1 y) : AlgebraicClosure (v.adicCompletion K.1)))
  rw [coe_idelesProj_of, coe_idelesProj_of]
  have h := finiteProj_smul_of_mem_stabilizer (placeOfEmbedding ι p.1) (localDecompHom ι p.1 σ) y
  have h' := congrArg (fun u : ((placeOfEmbedding ι p.1).1.adicCompletion p.1.1)ˣ =>
    (u : (placeOfEmbedding ι p.1).1.adicCompletion p.1.1)) h
  simp only [coe_finiteProj] at h'
  rw [h']
  exact completionEmbedding_smul ι p.1 σ _

def idelesLocalMor :
    Rep.res (globalDecomp (v.adicCompletion K.1) ι) (limitRep K) ⟶
      galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (idelesProj ι)).toIntLinearMap,
    fun σ => LinearMap.ext fun z => congrArg Additive.ofMul (idelesProj_smul ι σ z.toMul)⟩

@[simp]
theorem idelesLocalMor_hom_apply (z : Additive IdeleLimit) :
    (idelesLocalMor ι).hom z = Additive.ofMul (idelesProj ι z.toMul) :=
  rfl

def idelesLocalRes (n : ℕ) :
    cohomology (limitRep K) n ⟶
      cohomology (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n :=
  cohomologyMapAlong (globalDecomp (v.adicCompletion K.1) ι) (continuous_globalDecomp _ ι) (idelesLocalMor ι) n

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

def infIdelesLevelProj (F : FiniteSubfield) [Fact (K ≤ F)] :
    IdeleGroup F.1 →* (AlgebraicClosure v.Completion)ˣ :=
  (Units.map (infCompletionEmbedding ι F).toRingHom.toMonoidHom).comp
    (infiniteProj (infPlaceOfEmbedding ι F : InfinitePlace F.1))

theorem coe_infIdelesLevelProj (F : FiniteSubfield) [Fact (K ≤ F)] (x : IdeleGroup F.1) :
    ((infIdelesLevelProj ι F x : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) =
      infCompletionEmbedding ι F ((x : 𝔸[F.1]).1
        (infPlaceOfEmbedding ι F : InfinitePlace F.1)) :=
  rfl

theorem infIdelesLevelProj_ideleMap {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] (h : F ≤ E)
    (x : IdeleGroup F.1) : infIdelesLevelProj ι E (ideleMap h x) = infIdelesLevelProj ι F x := by
  have : Fact (F ≤ E) := ⟨h⟩
  apply Units.ext
  rw [coe_infIdelesLevelProj, coe_infIdelesLevelProj, ← infCompletionEmbedding_completionMap ι (F := F) (E := E)]
  congr 1
  exact ideleEmbedding_fst_of_comap_eq (infPlaceOfEmbedding ι E : InfinitePlace E.1)
    (infPlaceOfEmbedding ι F : InfinitePlace F.1)
    (InfinitePlace.LiesOver.comap_eq _ _) x

def infIdelesProj : IdeleLimit →* (AlgebraicClosure v.Completion)ˣ :=
  IdeleLimit.lift (fun F => (infIdelesLevelProj ι (joinField K F)).comp (ideleMap (le_joinField_right K F)))
    fun F E h x => by
      change infIdelesLevelProj ι (joinField K E) (ideleMap _ (ideleMap h x)) =
        infIdelesLevelProj ι (joinField K F) (ideleMap _ x)
      rw [ideleMap_ideleMap, ← infIdelesLevelProj_ideleMap ι (joinField_mono K h), ideleMap_ideleMap]

theorem infIdelesProj_of (F : FiniteSubfield) [Fact (K ≤ F)] (x : IdeleGroup F.1) :
    infIdelesProj ι (of F x) = infIdelesLevelProj ι F x :=
  infIdelesLevelProj_ideleMap ι (le_joinField_right K F) x

theorem coe_infIdelesProj_of (F : FiniteSubfield) [Fact (K ≤ F)] (x : IdeleGroup F.1) :
    ((infIdelesProj ι (of F x) : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) =
      infCompletionEmbedding ι F ((x : 𝔸[F.1]).1
        (infPlaceOfEmbedding ι F : InfinitePlace F.1)) := by
  rw [infIdelesProj_of, coe_infIdelesLevelProj]

theorem coe_infLocalDecompHom_eq_restrictHom (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]
    (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    ((infLocalDecompHom ι F σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1)
        (infPlaceOfEmbedding ι F : InfinitePlace F.1)) : F.1 ≃ₐ[K.1] F.1) =
      restrictHom (E := F) (globalDecomp v.Completion ι σ) :=
  decompHom_eq_restrictHom_globalDecomp _ ι F (infEmbedLevel ι F) (infEmbedLevel_apply ι F) σ

theorem infIdelesProj_smul (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) (z : IdeleLimit) :
    infIdelesProj ι ((globalDecomp v.Completion ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) • z) = σ • infIdelesProj ι z := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) F
  rw [← of_ideleMap hp x]
  generalize ideleMap hp x = y
  rw [smul_of_restrictHom, ← coe_infLocalDecompHom_eq_restrictHom ι p.1 σ]
  apply Units.ext
  change _ = σ ((infIdelesProj ι (of p.1 y) : AlgebraicClosure v.Completion))
  rw [coe_infIdelesProj_of, coe_infIdelesProj_of]
  have h := infiniteProj_smul_of_mem_stabilizer (infPlaceOfEmbedding ι p.1) (infLocalDecompHom ι p.1 σ) y
  have h' := congrArg (fun u : ((infPlaceOfEmbedding ι p.1 : InfinitePlace p.1.1).Completion)ˣ =>
    (u : (infPlaceOfEmbedding ι p.1 : InfinitePlace p.1.1).Completion)) h
  simp only [coe_infiniteProj] at h'
  rw [h']
  exact infCompletionEmbedding_smul ι p.1 σ _

def infIdelesLocalMor :
    Rep.res (globalDecomp v.Completion ι) (limitRep K) ⟶ galUnitsZ v.Completion (AlgebraicClosure v.Completion) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (infIdelesProj ι)).toIntLinearMap,
    fun σ => LinearMap.ext fun z => congrArg Additive.ofMul (infIdelesProj_smul ι σ z.toMul)⟩

@[simp]
theorem infIdelesLocalMor_hom_apply (z : Additive IdeleLimit) :
    (infIdelesLocalMor ι).hom z = Additive.ofMul (infIdelesProj ι z.toMul) :=
  rfl

def infIdelesLocalRes (n : ℕ) :
    cohomology (limitRep K) n ⟶ cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n :=
  cohomologyMapAlong (globalDecomp v.Completion ι) (continuous_globalDecomp _ ι) (infIdelesLocalMor ι) n

end Infinite

end

end GroundTheory.ProfCoh
