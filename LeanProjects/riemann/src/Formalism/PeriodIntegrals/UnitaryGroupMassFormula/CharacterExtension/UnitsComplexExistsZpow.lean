import Mathlib
import Formalism.PeriodIntegrals.CharExtend

namespace PI.CharExtendWork

theorem units_complex_exists_zpow (a : ℂˣ) (n : ℤ) (hn : n ≠ 0) : ∃ x : ℂˣ, x ^ n = a := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact a.ne_zero hz.symm
  set u : ℂˣ := Units.mk0 z hz0 with hu
  have hu' : u ^ n.natAbs = a := by
    ext
    simp [hu, hz]
  rcases Int.natAbs_eq n with h | h
  · refine ⟨u, ?_⟩
    rw [h, zpow_natCast, hu']
  · refine ⟨u⁻¹, ?_⟩
    rw [h, inv_zpow', neg_neg, zpow_natCast, hu']

noncomputable def divisibleUnitsComplex : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if h : n = 0 then 0 else
    Additive.ofMul (Classical.choose (units_complex_exists_zpow a.toMul n h))
  div_zero a := by simp
  div_cancel {n} a hn := by
    rw [dif_neg hn, ← ofMul_zpow, Classical.choose_spec (units_complex_exists_zpow a.toMul n hn)]
    rfl

theorem charExtend_main : PI.CharExtend := by
  intro G _ H χ
  letI : DivisibleBy (Additive ℂˣ) ℤ := divisibleUnitsComplex
  have hB : Module.Baer ℤ (Additive ℂˣ) := Module.Baer.of_divisible (Additive ℂˣ)
  let f : Additive H →+ Additive G := MonoidHom.toAdditive H.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.val_injective hxy
  obtain ⟨h, hh⟩ := hB.extension_property_addMonoidHom f hf (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

end PI.CharExtendWork
