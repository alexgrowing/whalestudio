import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleDual

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace GroundTheory.Arith.SchemeCoh

section
variable {X : Scheme.{u}}

lemma toSkeleton_dualSheaf_mul {L : X.Modules} (hL : IsInvertibleSheaf L) :
    toSkeleton (dualSheaf L) * toSkeleton L = 1 := by
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  have := isIso_dualEval hL
  exact congr_toSkeleton_of_iso (asIso (dualEval L))

noncomputable def unitOfInvertible {L : X.Modules} (hL : IsInvertibleSheaf L) :
    (Skeleton X.Modules)ˣ where
  val := toSkeleton L
  inv := toSkeleton (dualSheaf L)
  val_inv := by rw [mul_comm]; exact toSkeleton_dualSheaf_mul hL
  inv_val := toSkeleton_dualSheaf_mul hL

end

variable (X : Scheme.{u})

noncomputable def picardSubgroup : Subgroup (Skeleton X.Modules)ˣ where
  carrier := {v | ∃ L : X.Modules, IsInvertibleSheaf L ∧ toSkeleton L = (v : Skeleton X.Modules)}
  mul_mem' := by
    rintro v w ⟨L, hL, hv⟩ ⟨M, hM, hw⟩
    exact ⟨L ⊗ M, hL.tensor hM, by rw [Units.val_mul, Skeleton.toSkeleton_tensorObj, hv, hw]⟩
  one_mem' := ⟨𝟙_ X.Modules, isInvertibleSheaf_unit, rfl⟩
  inv_mem' := by
    rintro v ⟨L, hL, hv⟩
    refine ⟨dualSheaf L, hL.dual, ?_⟩
    change toSkeleton (dualSheaf L) = ((v⁻¹ : (Skeleton X.Modules)ˣ) : Skeleton X.Modules)
    apply Units.eq_inv_of_mul_eq_one_left
    rw [← hv, mul_comm]
    exact toSkeleton_dualSheaf_mul hL

abbrev Pic : Type (u + 1) := ↥(picardSubgroup X)

variable {X}

namespace Pic

noncomputable def mk (L : X.Modules) (hL : IsInvertibleSheaf L) : Pic X :=
  ⟨unitOfInvertible hL, L, hL, rfl⟩

def toClass (p : Pic X) : Skeleton X.Modules := ((p : ↥(picardSubgroup X)) : (Skeleton X.Modules)ˣ)

theorem mk_eq_mk_iff {L M : X.Modules} (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) :
    mk L hL = mk M hM ↔ Nonempty (L ≅ M) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  constructor
  · intro h
    exact congrArg toClass h
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact h

theorem exists_mk (p : Pic X) : ∃ (L : X.Modules) (hL : IsInvertibleSheaf L), mk L hL = p := by
  obtain ⟨v, L, hL, hv⟩ := p
  refine ⟨L, hL, Subtype.ext (Units.ext ?_)⟩
  exact hv

theorem mk_tensor {L M : X.Modules} (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) :
    mk (L ⊗ M) (hL.tensor hM) = mk L hL * mk M hM := by
  apply Subtype.ext
  apply Units.ext
  exact Skeleton.toSkeleton_tensorObj L M

theorem mk_unit : mk (𝟙_ X.Modules) isInvertibleSheaf_unit = 1 := by
  apply Subtype.ext
  apply Units.ext
  rfl

theorem mk_dualSheaf {L : X.Modules} (hL : IsInvertibleSheaf L) :
    mk (dualSheaf L) hL.dual = (mk L hL)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← mk_tensor, ← mk_unit, mk_eq_mk_iff]
  have := isIso_dualEval hL
  exact ⟨asIso (dualEval L)⟩

theorem mk_eq_one_iff {L : X.Modules} (hL : IsInvertibleSheaf L) :
    mk L hL = 1 ↔ Nonempty (L ≅ 𝟙_ X.Modules) := by
  rw [← mk_unit, mk_eq_mk_iff]

end Pic

end GroundTheory.Arith.SchemeCoh
