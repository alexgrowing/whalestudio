import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField IntermediateField GroundTheory.Global
  GroundTheory.Global.SemiLocal FiniteSubfield

open scoped TensorProduct Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Idempotents

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Semiring (A i)]
  {R : Type*} [CommRing R] [IsDomain R]

theorem exists_unique_map_single_one_eq_one (φ : (∀ i, A i) →+* R) :
    ∃! i, φ (Pi.single i 1) = 1 := by
  have hidem : ∀ i, φ (Pi.single i 1) = 0 ∨ φ (Pi.single i 1) = 1 := fun i ↦ by
    refine IsIdempotentElem.iff_eq_zero_or_one.1 ?_
    rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, one_mul]
  have hsum : ∑ i, φ (Pi.single i 1) = 1 := by
    have h1 : ∑ i, Pi.single i (1 : A i) = (1 : ∀ i, A i) := Finset.univ_sum_single 1
    rw [← map_sum, h1, map_one]
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, φ (Pi.single i 1) ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero h] at hsum
    exact zero_ne_one hsum
  refine ⟨i, (hidem i).resolve_left hi, fun j hj ↦ ?_⟩
  by_contra hji
  have h0 : Pi.single j (1 : A j) * Pi.single i 1 = 0 := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [hji]
    · simp [hk]
  have := congrArg φ h0
  rw [map_mul, map_zero, hj, (hidem i).resolve_left hi, one_mul] at this
  exact one_ne_zero this

omit [Fintype ι] [IsDomain R] in

theorem map_eq_map_single_of_map_single_one {φ : (∀ i, A i) →+* R} {i : ι}
    (hi : φ (Pi.single i 1) = 1) (y : ∀ i, A i) : φ y = φ (Pi.single i (y i)) := by
  have h : Pi.single i (1 : A i) * y = Pi.single i (y i) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  rw [← h, map_mul, hi, one_mul]

end Idempotents

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}

instance isScalarTower_finiteSubfield_algebraicClosure (F : FiniteSubfield) [Fact (K ≤ F)] :
    IsScalarTower K.1 F.1 ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

variable (F : FiniteSubfield) [Fact (K ≤ F)]

def embedLevel : F.1 →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1) :=
  ι.comp (IsScalarTower.toAlgHom K.1 F.1 ℚ̄)

@[simp]
theorem embedLevel_apply (x : F.1) : embedLevel ι F x = ι x :=
  rfl

def tensorLift :
    CompletionsOver F.1 v →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
  (Algebra.TensorProduct.lift (Algebra.ofId _ _) (embedLevel ι F)
    (fun _ _ ↦ Commute.all _ _)).comp (tensorEquiv F.1 v).symm.toAlgHom

theorem tensorLift_tensorEquiv (t : v.adicCompletion K.1 ⊗[K.1] F.1) :
    tensorLift ι F (tensorEquiv F.1 v t) = Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (embedLevel ι F) (fun _ _ ↦ Commute.all _ _) t := by
  simp [tensorLift]

theorem tensorLift_tensorEquiv_tmul (a : v.adicCompletion K.1) (x : F.1) :
    tensorLift ι F (tensorEquiv F.1 v (a ⊗ₜ x)) =
      algebraMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) a * ι x := by
  rw [tensorLift_tensorEquiv, Algebra.TensorProduct.lift_tmul]
  rfl

theorem tensorLift_algebraMap (x : F.1) :
    tensorLift ι F (algebraMap F.1 (CompletionsOver F.1 v) x) = ι x := by
  rw [← tensorEquiv_one_tmul, tensorLift_tensorEquiv]
  simp

open Classical in
theorem exists_unique_tensorLift_single :
    ∃! w : PlacesOver F.1 v, tensorLift ι F (Pi.single w 1) = 1 :=
  exists_unique_map_single_one_eq_one (tensorLift ι F).toRingHom

def placeOfEmbedding : PlacesOver F.1 v :=
  (exists_unique_tensorLift_single ι F).exists.choose

open Classical in
theorem tensorLift_single_placeOfEmbedding :
    tensorLift ι F (Pi.single (placeOfEmbedding ι F) 1) = 1 := by
  exact (exists_unique_tensorLift_single ι F).exists.choose_spec

open Classical in
theorem eq_placeOfEmbedding_of_tensorLift {w : PlacesOver F.1 v}
    (h : tensorLift ι F (Pi.single w 1) = 1) : w = placeOfEmbedding ι F :=
  (exists_unique_tensorLift_single ι F).unique h (tensorLift_single_placeOfEmbedding ι F)

theorem pi_single_algebraMap_eq {w : PlacesOver F.1 v} [DecidableEq (PlacesOver F.1 v)]
    (a : v.adicCompletion K.1) :
    Pi.single w (algebraMap (v.adicCompletion K.1) (w.1.adicCompletion F.1) a) =
      algebraMap (v.adicCompletion K.1) (CompletionsOver F.1 v) a * Pi.single w 1 := by
  funext u
  by_cases hu : u = w
  · subst hu
    simp
  · simp [hu]

open Classical in

def completionEmbedding :
    (placeOfEmbedding ι F).1.adicCompletion F.1 →ₐ[v.adicCompletion K.1]
      AlgebraicClosure (v.adicCompletion K.1) where
  toFun x := tensorLift ι F (Pi.single (placeOfEmbedding ι F) x)
  map_one' := tensorLift_single_placeOfEmbedding ι F
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' a := by
    rw [pi_single_algebraMap_eq, map_mul, AlgHom.commutes, tensorLift_single_placeOfEmbedding,
      mul_one]

theorem tensorLift_eq (y : CompletionsOver F.1 v) :
    tensorLift ι F y = completionEmbedding ι F (y (placeOfEmbedding ι F)) := by
  classical
  exact map_eq_map_single_of_map_single_one (φ := (tensorLift ι F).toRingHom)
    (tensorLift_single_placeOfEmbedding ι F) y

@[simp]
theorem completionEmbedding_algebraMap (x : F.1) :
    completionEmbedding ι F (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) x) = ι x := by
  rw [← tensorLift_algebraMap ι F x, tensorLift_eq]
  rfl

theorem algHom_ext_adicCompletion {B : Type*} [Semiring B] [Algebra K.1 B]
    [Algebra (v.adicCompletion K.1) B] [IsScalarTower K.1 (v.adicCompletion K.1) B]
    {w : PlacesOver F.1 v} {f g : w.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] B}
    (h : ∀ x : F.1, f (algebraMap F.1 _ x) = g (algebraMap F.1 _ x)) : f = g := by
  have key : (f.comp (Pi.evalAlgHom _ _ w)).comp (tensorEquiv F.1 v).toAlgHom =
      (g.comp (Pi.evalAlgHom _ _ w)).comp (tensorEquiv F.1 v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a x
    change f ((tensorEquiv F.1 v (a ⊗ₜ x)) w) = g ((tensorEquiv F.1 v (a ⊗ₜ x)) w)
    rw [tensorEquiv_tmul, Pi.mul_apply, map_mul, map_mul]
    congr 1
    · change f (algebraMap _ _ a) = g (algebraMap _ _ a)
      rw [AlgHom.commutes, AlgHom.commutes]
    · exact h x
  ext y
  classical
  obtain ⟨t, ht⟩ := (tensorEquiv F.1 v).surjective (Pi.single w y)
  have := DFunLike.congr_fun key t
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at this
  rw [show (tensorEquiv F.1 v).toAlgHom t = tensorEquiv F.1 v t from rfl, ht,
    Pi.single_eq_same] at this
  exact this

theorem eq_placeOfEmbedding {w : PlacesOver F.1 v}
    (j : w.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1))
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) : w = placeOfEmbedding ι F := by
  classical
  have key : tensorLift ι F = j.comp (Pi.evalAlgHom _ _ w) := by
    have : (tensorLift ι F).comp (tensorEquiv F.1 v).toAlgHom =
        (j.comp (Pi.evalAlgHom _ _ w)).comp (tensorEquiv F.1 v).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro a x
      change tensorLift ι F (tensorEquiv F.1 v (a ⊗ₜ x)) = j ((tensorEquiv F.1 v (a ⊗ₜ x)) w)
      rw [tensorLift_tensorEquiv_tmul, tensorEquiv_tmul, Pi.mul_apply, map_mul, ← hj x]
      congr 1
      exact (j.commutes a).symm
    ext y
    obtain ⟨t, rfl⟩ := (tensorEquiv F.1 v).surjective y
    exact DFunLike.congr_fun this t
  apply eq_placeOfEmbedding_of_tensorLift
  refine (DFunLike.congr_fun key _).trans ?_
  rw [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one]

section Decomposition

variable [F.1.fixingSubgroup.Normal]

theorem decompHom_smul_placeOfEmbedding
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHom (v.adicCompletion K.1) (embedLevel ι F) σ • placeOfEmbedding ι F =
      placeOfEmbedding ι F := by
  set τ := decompHom (v.adicCompletion K.1) (embedLevel ι F) σ
  set w₀ := placeOfEmbedding ι F
  have hu : w₀.1 = τ • (τ⁻¹ • w₀).1 := eq_smul_inv_smul v τ w₀
  let j := σ.symm.toAlgHom.comp
    ((completionEmbedding ι F).comp (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu).toAlgHom)
  have hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x := by
    intro x
    change σ.symm (completionEmbedding ι F (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu
      (algebraMap F.1 _ x))) = ι x
    rw [galEquiv_algebraMap, completionEmbedding_algebraMap]
    have h := decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x
    rw [embedLevel_apply, embedLevel_apply] at h
    rw [h, AlgEquiv.symm_apply_apply]
  have h := eq_placeOfEmbedding ι F j hj
  calc τ • w₀ = τ • (τ⁻¹ • w₀) := by rw [h]
    _ = w₀ := smul_inv_smul τ w₀

def localDecompHom :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →*
      MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal :=
  (decompHom (v.adicCompletion K.1) (embedLevel ι F)).codRestrict _ fun σ ↦
    MulAction.mem_stabilizer_iff.2
      (congrArg (fun u : PlacesOver F.1 v ↦ u.1.asIdeal) (decompHom_smul_placeOfEmbedding ι F σ))

theorem coe_localDecompHom
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    (localDecompHom ι F σ : Gal(F.1/K.1)) = decompHom (v.adicCompletion K.1) (embedLevel ι F) σ :=
  rfl

theorem ι_localDecompHom_apply
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) (x : F.1) :
    ι ((localDecompHom ι F σ : Gal(F.1/K.1)) x : F.1) = σ (ι x) :=
  decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x

theorem continuous_localDecompHom : Continuous (localDecompHom ι F) :=
  (continuous_decompHom (embedLevel ι F)).subtype_mk _

theorem completionEmbedding_smul
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (y : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    completionEmbedding ι F (localDecompHom ι F σ • y) = σ (completionEmbedding ι F y) := by
  have : (completionEmbedding ι F).comp
      (decompositionAlgEquiv v (placeOfEmbedding ι F).1 (localDecompHom ι F σ)).toAlgHom =
      σ.toAlgHom.comp (completionEmbedding ι F) := by
    apply algHom_ext_adicCompletion
    intro x
    change completionEmbedding ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1
      (localDecompHom ι F σ) (algebraMap F.1 _ x)) = σ (completionEmbedding ι F (algebraMap F.1 _ x))
    rw [decompositionAlgEquiv_algebraMap, completionEmbedding_algebraMap,
      completionEmbedding_algebraMap, ι_localDecompHom_apply]
  exact DFunLike.congr_fun this y

def localUnitsMor :
    Rep.res (localDecompHom ι F) (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal)
      ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) ⟶
      galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (completionEmbedding ι F).toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ ↦ LinearMap.ext fun x ↦
      congrArg Additive.ofMul (Units.ext (completionEmbedding_smul ι F σ
        ((Additive.toMul x : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) :
          (placeOfEmbedding ι F).1.adicCompletion F.1)))⟩

@[simp]
theorem localUnitsMor_hom_apply (x : Additive ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) :
    ((Additive.toMul ((localUnitsMor ι F).hom x) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
      AlgebraicClosure (v.adicCompletion K.1)) =
      completionEmbedding ι F (x.toMul : (placeOfEmbedding ι F).1.adicCompletion F.1) :=
  rfl

def localInfl (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal)
      ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) n ⟶
      cohomology (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n :=
  cohomologyMapAlong (localDecompHom ι F) (continuous_localDecompHom ι F) (localUnitsMor ι F) n

end Decomposition

end

end GroundTheory.ProfCoh
