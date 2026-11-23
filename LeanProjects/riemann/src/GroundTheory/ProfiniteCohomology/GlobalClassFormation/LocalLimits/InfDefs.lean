import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield
  NumberField.InfinitePlace.Completion

open scoped TensorProduct Pointwise NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

variable (F : FiniteSubfield) [Fact (K ≤ F)]

def infEmbedLevel : F.1 →ₐ[K.1] AlgebraicClosure v.Completion :=
  ι.comp (IsScalarTower.toAlgHom K.1 F.1 ℚ̄)

@[simp]
theorem infEmbedLevel_apply (x : F.1) : infEmbedLevel ι F x = ι x :=
  rfl

instance (v : NumberField.InfinitePlace K.1) : Finite (v.placesOver F.1) := inferInstance

def infTensorLift :
    GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v →ₐ[v.Completion]
      AlgebraicClosure v.Completion :=
  (Algebra.TensorProduct.lift (Algebra.ofId _ _) (infEmbedLevel ι F)
    (fun _ _ ↦ Commute.all _ _)).comp
      (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).symm.toAlgHom

theorem infTensorLift_tensorPiEquiv' (t : v.Completion ⊗[K.1] F.1) :
    infTensorLift ι F (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v t) =
      Algebra.TensorProduct.lift (Algebra.ofId _ _) (infEmbedLevel ι F)
        (fun _ _ ↦ Commute.all _ _) t := by
  simp [infTensorLift, -GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply]

theorem infTensorLift_tensorPiEquiv (a : v.Completion) (x : F.1) :
    infTensorLift ι F (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) =
      algebraMap v.Completion (AlgebraicClosure v.Completion) a * ι x := by
  rw [infTensorLift_tensorPiEquiv', Algebra.TensorProduct.lift_tmul]
  rfl

theorem infTensorLift_algebraMap (x : F.1) :
    infTensorLift ι F (algebraMap F.1 (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) x) =
      ι x := by
  have : algebraMap F.1 (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) x =
      GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (1 ⊗ₜ x) := by
    funext w
    rw [GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply,
      GroundTheory.Global.InfinitePlace.tensorPiHom_tmul, map_one, one_mul]
    rfl
  rw [this, infTensorLift_tensorPiEquiv, map_one, one_mul]

open Classical in
theorem exists_unique_infTensorLift_single :
    ∃! w : v.placesOver F.1, infTensorLift ι F (Pi.single w 1) = 1 := by
  have := Fintype.ofFinite (v.placesOver F.1)
  exact exists_unique_map_single_one_eq_one (infTensorLift ι F).toRingHom

def infPlaceOfEmbedding : v.placesOver F.1 :=
  (exists_unique_infTensorLift_single ι F).exists.choose

open Classical in
theorem infTensorLift_single_infPlaceOfEmbedding :
    infTensorLift ι F (Pi.single (infPlaceOfEmbedding ι F) 1) = 1 :=
  (exists_unique_infTensorLift_single ι F).exists.choose_spec

open Classical in
theorem eq_infPlaceOfEmbedding_of_infTensorLift {w : v.placesOver F.1}
    (h : infTensorLift ι F (Pi.single w 1) = 1) : w = infPlaceOfEmbedding ι F :=
  (exists_unique_infTensorLift_single ι F).unique h (infTensorLift_single_infPlaceOfEmbedding ι F)

theorem pi_single_algebraMap_eq_infinite {w : v.placesOver F.1} [DecidableEq (v.placesOver F.1)]
    (a : v.Completion) :
    Pi.single w (algebraMap v.Completion (w : NumberField.InfinitePlace F.1).Completion a) =
      algebraMap v.Completion (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) a *
        Pi.single w 1 := by
  funext u
  by_cases hu : u = w
  · subst hu
    simp
  · simp [hu]

open Classical in

def infCompletionEmbedding :
    (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion where
  toFun x := infTensorLift ι F (Pi.single (infPlaceOfEmbedding ι F) x)
  map_one' := infTensorLift_single_infPlaceOfEmbedding ι F
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by
    rw [Pi.single_add]
    exact (infTensorLift ι F).toRingHom.map_add _ _
  commutes' a := by
    rw [pi_single_algebraMap_eq_infinite, map_mul, AlgHom.commutes,
      infTensorLift_single_infPlaceOfEmbedding, mul_one]

theorem infTensorLift_eq (y : GroundTheory.Global.InfinitePlace.PiPlacesOver (L := F.1) v) :
    infTensorLift ι F y = infCompletionEmbedding ι F (y (infPlaceOfEmbedding ι F)) := by
  classical
  have := Fintype.ofFinite (v.placesOver F.1)
  exact map_eq_map_single_of_map_single_one (φ := (infTensorLift ι F).toRingHom)
    (infTensorLift_single_infPlaceOfEmbedding ι F) y

@[simp]
theorem infCompletionEmbedding_algebraMap (x : F.1) :
    infCompletionEmbedding ι F
      (algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion x) =
      ι x := by
  rw [← infTensorLift_algebraMap ι F x, infTensorLift_eq]
  rfl

theorem algHom_ext_infCompletion {B : Type*} [Semiring B] [Algebra K.1 B]
    [Algebra v.Completion B] [IsScalarTower K.1 v.Completion B] {w : v.placesOver F.1}
    {f g : (w : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion] B}
    (h : ∀ x : F.1, f (algebraMap F.1 _ x) = g (algebraMap F.1 _ x)) : f = g := by
  have key : (f.comp (Pi.evalAlgHom _ _ w)).comp
        (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom =
      (g.comp (Pi.evalAlgHom _ _ w)).comp
        (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a x
    change f ((GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) w) =
      g ((GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) w)
    rw [GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply,
      GroundTheory.Global.InfinitePlace.tensorPiHom_tmul, map_mul, map_mul]
    congr 1
    · rw [AlgHom.commutes, AlgHom.commutes]
    · exact h x
  ext y
  classical
  obtain ⟨t, ht⟩ := (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).surjective
    (Pi.single w y)
  have := DFunLike.congr_fun key t
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at this
  rw [show (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom t =
    GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v t from rfl, ht,
    Pi.single_eq_same] at this
  exact this

theorem eq_infPlaceOfEmbedding {w : v.placesOver F.1}
    (j : (w : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion)
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) : w = infPlaceOfEmbedding ι F := by
  classical
  have key : infTensorLift ι F = j.comp (Pi.evalAlgHom _ _ w) := by
    have : (infTensorLift ι F).comp
          (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom =
        (j.comp (Pi.evalAlgHom _ _ w)).comp
          (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro a x
      change infTensorLift ι F (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) =
        j ((GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v (a ⊗ₜ x)) w)
      rw [infTensorLift_tensorPiEquiv, GroundTheory.Global.InfinitePlace.tensorPiEquiv_apply,
        GroundTheory.Global.InfinitePlace.tensorPiHom_tmul, map_mul, ← hj x]
      congr 1
      exact (j.commutes a).symm
    ext y
    obtain ⟨t, rfl⟩ := (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := F.1) v).surjective y
    exact DFunLike.congr_fun this t
  apply eq_infPlaceOfEmbedding_of_infTensorLift
  refine (DFunLike.congr_fun key _).trans ?_
  rw [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one]

section Decomposition

theorem infiniteCompletionMap_algebraMap_completion (τ : F.1 ≃ₐ[K.1] F.1)
    (w' : NumberField.InfinitePlace F.1) [w'.LiesOver v]
    [(w'.comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).LiesOver v] (c : v.Completion) :
    AdeleBaseChange.infiniteCompletionMap (τ : F.1 ≃+* F.1) w'
      (algebraMap v.Completion (w'.comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).Completion c) =
      algebraMap v.Completion w'.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((continuous_infiniteCompletionMap _ w').comp (continuous_algebraMap v.Completion
      (w'.comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).Completion))
    (continuous_algebraMap v.Completion w'.Completion) (funext fun a ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    change AdeleBaseChange.infiniteCompletionMap (τ : F.1 ≃+* F.1) w'
      (algebraMap v.Completion _ (algebraMap K.1 v.Completion (WithAbs.ofAbs a))) =
      algebraMap v.Completion w'.Completion (algebraMap K.1 v.Completion (WithAbs.ofAbs a))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K.1 F.1, AdeleBaseChange.infiniteCompletionMap_algebraMap,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

variable [F.1.fixingSubgroup.Normal]

theorem decompHom_smul_infPlaceOfEmbedding (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    decompHom v.Completion (infEmbedLevel ι F) σ • (infPlaceOfEmbedding ι F :
      NumberField.InfinitePlace F.1) = infPlaceOfEmbedding ι F := by
  set τ := decompHom v.Completion (infEmbedLevel ι F) σ
  set w₀ := infPlaceOfEmbedding ι F
  have hcomap : (w₀ : NumberField.InfinitePlace F.1).comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1) =
      τ⁻¹ • (w₀ : NumberField.InfinitePlace F.1) :=
    AdeleBaseChange.comap_eq_inv_smul τ w₀
  have hu : ((w₀ : NumberField.InfinitePlace F.1).comap
      ((τ : F.1 ≃+* F.1) : F.1 →+* F.1)).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap,
      GroundTheory.Global.InfinitePlace.comap_smul_algebraMap,
      ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact w₀.2
  let u : v.placesOver F.1 := ⟨_, hu⟩
  let j : (u : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion]
      AlgebraicClosure v.Completion :=
    σ.symm.toAlgHom.comp ((infCompletionEmbedding ι F).comp
      { AdeleBaseChange.infiniteCompletionMap (τ : F.1 ≃+* F.1) w₀ with
        commutes' := infiniteCompletionMap_algebraMap_completion F τ w₀ })
  have hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x := by
    intro x
    change σ.symm (infCompletionEmbedding ι F (AdeleBaseChange.infiniteCompletionMap
      (τ : F.1 ≃+* F.1) w₀ (algebraMap F.1 _ x))) = ι x
    rw [AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap]
    have h := decompHom_apply (Kv := v.Completion) (infEmbedLevel ι F) σ x
    rw [infEmbedLevel_apply, infEmbedLevel_apply] at h
    rw [AlgEquiv.coe_ringEquiv, h, AlgEquiv.symm_apply_apply]
  have h := congrArg Subtype.val (eq_infPlaceOfEmbedding ι F j hj)
  change (w₀ : NumberField.InfinitePlace F.1).comap ((τ : F.1 ≃+* F.1) : F.1 →+* F.1) =
    (w₀ : NumberField.InfinitePlace F.1) at h
  rw [hcomap] at h
  calc τ • (w₀ : NumberField.InfinitePlace F.1) = τ • (τ⁻¹ • (w₀ : NumberField.InfinitePlace F.1)) := by
        rw [h]
    _ = w₀ := smul_inv_smul τ _

def infLocalDecompHom :
    Gal(AlgebraicClosure v.Completion/v.Completion) →*
      MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) :=
  (decompHom v.Completion (infEmbedLevel ι F)).codRestrict _ fun σ ↦
    MulAction.mem_stabilizer_iff.2 (decompHom_smul_infPlaceOfEmbedding ι F σ)

theorem coe_infLocalDecompHom (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    (infLocalDecompHom ι F σ : Gal(F.1/K.1)) = decompHom v.Completion (infEmbedLevel ι F) σ :=
  rfl

theorem ι_infLocalDecompHom_apply (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) (x : F.1) :
    ι ((infLocalDecompHom ι F σ : Gal(F.1/K.1)) x : F.1) = σ (ι x) :=
  decompHom_apply (Kv := v.Completion) (infEmbedLevel ι F) σ x

theorem continuous_infLocalDecompHom : Continuous (infLocalDecompHom ι F) :=
  (continuous_decompHom (infEmbedLevel ι F)).subtype_mk _

theorem infCompletionEmbedding_smul (σ : Gal(AlgebraicClosure v.Completion/v.Completion))
    (y : (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :
    infCompletionEmbedding ι F (infLocalDecompHom ι F σ • y) = σ (infCompletionEmbedding ι F y) := by
  have : (infCompletionEmbedding ι F).comp (infiniteDecompositionAlgEquiv v
      (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) (infLocalDecompHom ι F σ)).toAlgHom =
      σ.toAlgHom.comp (infCompletionEmbedding ι F) := by
    apply algHom_ext_infCompletion
    intro x
    change infCompletionEmbedding ι F (infLocalDecompHom ι F σ • algebraMap F.1 _ x) =
      σ (infCompletionEmbedding ι F (algebraMap F.1 _ x))
    have e : infLocalDecompHom ι F σ • algebraMap F.1
        (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion x =
        algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
          ((infLocalDecompHom ι F σ : Gal(F.1/K.1)) x) :=
      infiniteDecomposition_smul_coe (infLocalDecompHom ι F σ) (WithAbs.toAbs _ x)
    rw [e, infCompletionEmbedding_algebraMap, infCompletionEmbedding_algebraMap,
      ι_infLocalDecompHom_apply]
  exact DFunLike.congr_fun this y

def infLocalUnitsMor :
    Rep.res (infLocalDecompHom ι F) (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
      ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) ⟶
      galUnitsZ v.Completion (AlgebraicClosure v.Completion) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (infCompletionEmbedding ι F).toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ ↦ LinearMap.ext fun x ↦
      congrArg Additive.ofMul (Units.ext (infCompletionEmbedding_smul ι F σ
        ((Additive.toMul x : ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
          (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)))⟩

@[simp]
theorem infLocalUnitsMor_hom_apply
    (x : Additive ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
    ((Additive.toMul ((infLocalUnitsMor ι F).hom x) : (AlgebraicClosure v.Completion)ˣ) :
      AlgebraicClosure v.Completion) =
      infCompletionEmbedding ι F (x.toMul :
        (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :=
  rfl

def infLocalInfl (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
      ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) n ⟶
      cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n :=
  cohomologyMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F)
    (infLocalUnitsMor ι F) n

end Decomposition

end

end GroundTheory.ProfCoh
