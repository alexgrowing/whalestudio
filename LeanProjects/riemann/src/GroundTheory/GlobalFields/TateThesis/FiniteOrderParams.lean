import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
set_option maxSynthPendingDepth 1

open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

open IdeleGroup

variable (χ : HeckeCharacter K)

theorem exists_toIdele_pow_eq_one (h : IsOfFinOrder χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : IdeleGroup K, χ.toIdele x ^ n = 1 := by
  obtain ⟨n, hn, hχ⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine ⟨n, hn, fun x ↦ ?_⟩
  rw [toIdele_apply, ← ContinuousMonoidHom.pow_apply, hχ]
  rfl

theorem realComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsReal) {x : ℝˣ} (hx : 0 < (x : ℝ)) : χ.realComponent hw x = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  have hr : 0 < (x : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
  have hy : Units.mk0 _ hr.ne' ^ n = x := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hx.le hn.ne'])
  rw [← hy, map_pow]
  exact hpow (infiniteEmbedding w (realUnitsHom hw (Units.mk0 _ hr.ne')))

theorem complexComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsComplex) (z : ℂˣ) : χ.complexComponent hw z = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact z.ne_zero hy.symm
  have hyz : Units.mk0 y hy0 ^ n = z := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])
  rw [← hyz, map_pow]
  exact hpow (infiniteEmbedding w (complexUnitsHom hw (Units.mk0 y hy0)))

end HeckeCharacter

end

end GroundTheory.Global
