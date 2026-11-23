import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal

open scoped Pointwise NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v) (w' : PlacesOver E.1 v)
  [hw : w'.1.asIdeal.LiesOver w.1.asIdeal]

theorem algebraMap_levelRestrict_integers (σ : E.1 ≃ₐ[K.1] E.1) (x : 𝓞 F.1) :
    algebraMap (𝓞 F.1) (𝓞 E.1) (levelRestrict K F E σ • x) = σ • algebraMap (𝓞 F.1) (𝓞 E.1) x :=
  RingOfIntegers.ext (coe_levelRestrict_apply σ (x : F.1))

include hw in

theorem levelRestrict_mem_stabilizer {σ : E.1 ≃ₐ[K.1] E.1}
    (hσ : σ ∈ MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal) :
    levelRestrict K F E σ ∈ MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have hover : w.1.asIdeal = w'.1.asIdeal.comap (algebraMap (𝓞 F.1) (𝓞 E.1)) := hw.over
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hover, Ideal.mem_comap, Ideal.mem_comap,
    ← map_inv, algebraMap_levelRestrict_integers, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hσ]

variable {w w'} in

def decompRestrict :
    MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal →*
      MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal where
  toFun σ := ⟨levelRestrict K F E σ, levelRestrict_mem_stabilizer w w' σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_decompRestrict (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal) :
    ((decompRestrict (w := w) σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal) :
      F.1 ≃ₐ[K.1] F.1) = levelRestrict K F E σ :=
  rfl

theorem completionMap_decomposition_smul (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
    (a : w.1.adicCompletion F.1) :
    completionMap w.1 w'.1 (decompRestrict (w := w) σ • a) = σ • completionMap w.1 w'.1 a := by
  have h1 := MulAction.mem_stabilizer_iff.1 (decompRestrict (w := w) σ).2
  have h2 := MulAction.mem_stabilizer_iff.1 σ.2
  have := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F.1) (K := F.1) w.1).equalizer
    ((continuous_completionMap w.1 w'.1).comp (continuous_adicCompletionRingHomOf _ h1))
    ((continuous_adicCompletionRingHomOf _ h2).comp (continuous_completionMap w.1 w'.1))
    (funext fun x => by
      simp only [Function.comp_apply]
      rw [adicCompletionRingHomOf_algebraMap, completionMap_algebraMap, completionMap_algebraMap]
      simp only [IsScalarTower.algebraMap_apply F.1 E.1 (w'.1.adicCompletion E.1)]
      rw [adicCompletionRingHomOf_algebraMap, coe_decompRestrict, coe_levelRestrict_apply])
  exact congrFun this a

variable {w w'} in

def completionUnitsRep :
    Rep.res (decompRestrict (w := w) (w' := w'))
        (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
          (w.1.adicCompletion F.1)ˣ) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
        (w'.1.adicCompletion E.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (completionMap w.1 w'.1 : w.1.adicCompletion F.1 →* w'.1.adicCompletion E.1))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => congrArg Additive.ofMul (Units.ext
      (completionMap_decomposition_smul w w' σ
        (Additive.toMul (α := (w.1.adicCompletion F.1)ˣ) a : w.1.adicCompletion F.1)))⟩

@[simp]
theorem completionUnitsRep_hom_apply (a : Additive (w.1.adicCompletion F.1)ˣ) :
    ((Additive.toMul (α := (w'.1.adicCompletion E.1)ˣ) ((completionUnitsRep (w := w) (w' := w')).hom a) :
      (w'.1.adicCompletion E.1)ˣ) : w'.1.adicCompletion E.1) =
      completionMap w.1 w'.1 (Additive.toMul (α := (w.1.adicCompletion F.1)ˣ) a : w.1.adicCompletion F.1) :=
  rfl

variable (K F E) in

def localTransition (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
        (w'.1.adicCompletion E.1)ˣ) n :=
  cohomologyMapAlong decompRestrict continuous_of_discreteTopology completionUnitsRep n

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1) (w' : v.placesOver E.1) [hw : w'.1.LiesOver w.1]

include hw in

theorem levelRestrict_mem_stabilizer_infinite {σ : E.1 ≃ₐ[K.1] E.1}
    (hσ : σ ∈ MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) :
    levelRestrict K F E σ ∈ MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1 := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have hover : w'.1.comap (algebraMap F.1 E.1) = w.1 := InfinitePlace.LiesOver.comap_eq w'.1 w.1
  have key : ∀ y : E.1, w'.1 (σ.symm y) = w'.1 y := fun y => by
    conv_rhs => rw [← hσ]
    rfl
  rw [← hover]
  refine InfinitePlace.ext _ _ fun x => ?_
  rw [InfinitePlace.smul_apply, InfinitePlace.comap_apply, InfinitePlace.comap_apply]
  have h1 : (levelRestrict K F E σ).symm x = levelRestrict K F E σ⁻¹ x := by
    rw [map_inv]
    rfl
  rw [h1, coe_levelRestrict_apply]
  exact key _

variable {w w'} in

def infDecompRestrict :
    MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1 →* MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1 where
  toFun σ := ⟨levelRestrict K F E σ, levelRestrict_mem_stabilizer_infinite w w' σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_infDecompRestrict (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) :
    ((infDecompRestrict (w := w) σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
      F.1 ≃ₐ[K.1] F.1) = levelRestrict K F E σ :=
  rfl

theorem infCompletionMap_decomposition_smul (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1)
    (a : w.1.Completion) :
    NumberField.LiesOver.completionMap (infDecompRestrict (w := w) σ • a) =
      σ • NumberField.LiesOver.completionMap (v := w.1) (w := w'.1) a := by
  have := (InfinitePlace.Completion.denseRange_coe w.1).equalizer
    ((NumberField.LiesOver.continuous_completionMap (v := w.1) (w := w'.1)).comp
      (continuous_completionRingHomOf (infDecompRestrict (w := w) σ).2))
    ((continuous_completionRingHomOf σ.2).comp
      (NumberField.LiesOver.continuous_completionMap (v := w.1) (w := w'.1)))
    (funext fun y => by
      simp only [Function.comp_apply]
      rw [completionRingHomOf_coe, NumberField.LiesOver.completionMap_coe,
        NumberField.LiesOver.completionMap_coe, completionRingHomOf_coe]
      refine congrArg (fun z : WithAbs (w'.1 : InfinitePlace E.1).1 => (z : w'.1.Completion))
        (WithAbs.ofAbs_injective _ ?_)
      rw [ofAbs_withAbsMapOf, WithAbs.ofAbs_algebraMap, WithAbs.ofAbs_algebraMap, ofAbs_withAbsMapOf,
        coe_infDecompRestrict, coe_levelRestrict_apply])
  exact congrFun this a

variable {w w'} in

def infCompletionUnitsRep :
    Rep.res (infDecompRestrict (w := w) (w' := w'))
        (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) (w'.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (NumberField.LiesOver.completionMap (v := w.1)
      (w := w'.1) : w.1.Completion →* w'.1.Completion))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => congrArg Additive.ofMul (Units.ext
      (infCompletionMap_decomposition_smul w w' σ
        (Additive.toMul (α := (w.1.Completion)ˣ) a : w.1.Completion)))⟩

@[simp]
theorem infCompletionUnitsRep_hom_apply (a : Additive (w.1.Completion)ˣ) :
    ((Additive.toMul (α := (w'.1.Completion)ˣ) ((infCompletionUnitsRep (w := w) (w' := w')).hom a) :
      (w'.1.Completion)ˣ) : w'.1.Completion) =
      NumberField.LiesOver.completionMap (v := w.1) (w := w'.1)
        (Additive.toMul (α := (w.1.Completion)ˣ) a : w.1.Completion) :=
  rfl

variable (K F E) in

def infLocalTransition (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1)
        (w'.1.Completion)ˣ) n :=
  cohomologyMapAlong infDecompRestrict continuous_of_discreteTopology infCompletionUnitsRep n

end Infinite

end

end GroundTheory.ProfCoh
