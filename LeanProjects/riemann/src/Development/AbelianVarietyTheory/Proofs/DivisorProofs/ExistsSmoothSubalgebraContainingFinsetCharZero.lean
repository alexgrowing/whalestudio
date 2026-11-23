import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAway
open scoped TensorProduct

namespace GlobalTheory

theorem exists_smooth_subalgebra_of_finset : ∀ (F K : Type) [Field F] [CharZero F] [Field K]
    [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧
      Algebra.Smooth F R := by
  intro F K _ _ _ _ s
  haveI : PerfectField F := PerfectField.ofCharZero
  let C : Subalgebra F K := Algebra.adjoin F (↑s : Set K)
  haveI : Algebra.FiniteType F C :=
    ⟨(Subalgebra.fg_top C).mpr (Subalgebra.fg_adjoin_finset s)⟩
  obtain ⟨f, hf0, hsm, -⟩ := GlobalTheory.SS.exists_smooth_free_away F C C
  have hinjC : Function.Injective (algebraMap C K) := Subtype.val_injective
  have hfK : IsUnit (algebraMap C K f) := by
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    exact hf0 (hinjC (by simpa using h))
  let g : Localization.Away f →ₐ[F] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => by
        show IsLocalization.Away.lift f hfK (algebraMap F (Localization.Away f) r) = algebraMap F K r
        rw [IsScalarTower.algebraMap_apply F C (Localization.Away f),
          IsLocalization.Away.lift_eq]
        rfl }
  have hginj : Function.Injective g := by
    show Function.Injective (IsLocalization.Away.lift f hfK)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0) h]
    · intro h
      have : x = y := hinjC h
      rw [this]
  refine ⟨g.range, ?_, ?_⟩
  · intro x hx
    refine ⟨algebraMap C (Localization.Away f) ⟨x, Algebra.subset_adjoin hx⟩, ?_⟩
    show IsLocalization.Away.lift f hfK _ = x
    rw [IsLocalization.Away.lift_eq]
    rfl
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective g hginj)
end GlobalTheory
