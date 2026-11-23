import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace EstT

variable {l : ℕ} [Fact l.Prime]

theorem qB_mem_ainf (q : ℚ_[l]) : qB l q ∈ Ainf' l := by
  have key : ∀ z : ℤ_[l], qB l (algebraMap ℤ_[l] ℚ_[l] z) ∈ Ainf' l := fun z => by
    have e : qB l (algebraMap ℤ_[l] ℚ_[l] z) = zB l z := IsLocalization.lift_eq _ _
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨ainfMap l (zA l z), rfl⟩)
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ℤ_[l]) q
  have hs : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsu := PadicInt.unitCoeff_spec hs
  set u := PadicInt.unitCoeff hs
  set n := (s : ℤ_[l]).valuation
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have e : IsLocalization.mk' ℚ_[l] z s =
      algebraMap ℤ_[l] ℚ_[l] (z * ↑u⁻¹) * ((l : ℚ_[l])⁻¹) ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, hsu]
    simp only [map_mul, map_pow, map_natCast]
    have hx : ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hl0, one_pow]
    have hu : algebraMap ℤ_[l] ℚ_[l] (↑u⁻¹ : ℤ_[l]) * algebraMap ℤ_[l] ℚ_[l] (u : ℤ_[l]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap ℤ_[l] ℚ_[l] z) * ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n) * hu -
      algebraMap ℤ_[l] ℚ_[l] z * hx
  show qB l (IsLocalization.mk' ℚ_[l] z s) ∈ _
  rw [e, map_mul, map_pow]
  exact (Ainf' l).mul_mem (key _) ((Ainf' l).pow_mem (Subring.subset_closure (Or.inr rfl)) _)

theorem σC_coe (g : GQ l) (y : PadicAlgCl l) : σC g (y : ℂ_[l]) = ((g y : PadicAlgCl l) : ℂ_[l]) := by
  rw [σC, galCp_coe]
  rfl

end EstT

end period_ring_base
