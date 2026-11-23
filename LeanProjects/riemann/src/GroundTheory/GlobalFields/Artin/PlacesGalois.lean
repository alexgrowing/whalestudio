import Mathlib
import GroundTheory.GlobalFields.Artin.PlacesFrobenius
import GroundTheory.GlobalFields.Artin.PlacesInfinite
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

def fixedFieldMulEquiv : H ≃* Gal(L/fixedField H) where
  toFun := toFixedFieldAlgEquiv H
  invFun σ := ⟨σ.restrictScalars K, restrictScalars_mem H σ⟩
  left_inv _ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)
  right_inv _ := AlgEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ rfl

omit [IsGalois K L] in
@[simp]
theorem fixedFieldMulEquiv_apply (h : H) (y : L) : fixedFieldMulEquiv H h y = (h : Gal(L/K)) y :=
  rfl

omit [IsGalois K L] in
theorem fixedFieldMulEquiv_smul_ringOfIntegers (h : H) (y : 𝓞 L) :
    fixedFieldMulEquiv H h • y = h • y :=
  rfl

omit [IsGalois K L] in
theorem fixedFieldMulEquiv_smul_ideal (h : H) (P : Ideal (𝓞 L)) :
    fixedFieldMulEquiv H h • P = h • P := by
  rw [Ideal.pointwise_smul_def]
  change _ = (h : Gal(L/K)) • P
  rw [Ideal.pointwise_smul_def]
  rfl

omit [IsGalois K L] in

theorem stabilizer_fixedField_eq (P : Ideal (𝓞 L)) :
    MulAction.stabilizer Gal(L/fixedField H) P =
      (MulAction.stabilizer H P).map (fixedFieldMulEquiv H).toMonoidHom := by
  ext σ
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    ← fixedFieldMulEquiv_smul_ideal, MulEquiv.apply_symm_apply]

omit [IsGalois K L] in

theorem inertia_fixedField_eq (P : Ideal (𝓞 L)) :
    P.inertia Gal(L/fixedField H) = (P.inertia H).map (fixedFieldMulEquiv H).toMonoidHom := by
  ext σ
  rw [Subgroup.mem_map_equiv]
  change (∀ y, σ • y - y ∈ P) ↔ ∀ y, (fixedFieldMulEquiv H).symm σ • y - y ∈ P
  simp_rw [← fixedFieldMulEquiv_smul_ringOfIntegers, MulEquiv.apply_symm_apply]

theorem isArithFrobAt_fixedFieldMulEquiv_iff (h : H) (P : Ideal (𝓞 L)) :
    IsArithFrobAt (𝓞 (fixedField H)) (fixedFieldMulEquiv H h) P ↔
      IsArithFrobAt (𝓞 (fixedField H)) h P :=
  Iff.rfl

omit [IsGalois K L] in

theorem stabilizer_fixedField_smul_eq (w : HeightOneSpectrum (𝓞 L)) (x : Gal(L/K)) :
    MulAction.stabilizer Gal(L/fixedField H) (x • w.asIdeal) =
      ((MulAut.conj x • MulAction.stabilizer Gal(L/K) w.asIdeal : Subgroup Gal(L/K)).subgroupOf
        H).map (fixedFieldMulEquiv H).toMonoidHom := by
  rw [stabilizer_fixedField_eq]
  congr 1
  exact stabilizer_smul_eq H x w.asIdeal

omit [IsGalois K L] in

theorem inertia_fixedField_smul_eq (w : HeightOneSpectrum (𝓞 L)) (x : Gal(L/K)) :
    (x • w.asIdeal).inertia Gal(L/fixedField H) =
      ((MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H).map
        (fixedFieldMulEquiv H).toMonoidHom := by
  rw [inertia_fixedField_eq]
  congr 1
  exact inertia_smul_eq H x w.asIdeal

end GroundTheory.Global.Artin
