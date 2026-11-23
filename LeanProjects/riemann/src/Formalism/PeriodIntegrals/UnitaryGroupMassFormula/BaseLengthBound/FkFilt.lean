import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem fkFilt_holds : FkFilt := by
  intro D B P j X ka wL wF G la T
  refine ⟨?_, ?_, ?_⟩
  · intro k l hkl
    unfold Fk
    apply Submodule.span_mono
    apply Set.image_mono
    exact SetLike.coe_subset_coe.2 (Submodule.smul_mono_left (Ideal.pow_le_pow_right hkl))
  · unfold Fk
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ,
      (toWK_surjective X la G.w wF (a0 D j T)).range_eq, Submodule.span_univ]
  · unfold Fk
    rw [Submodule.span_eq_bot]
    rintro _ ⟨x, hx, rfl⟩
    exact (toWK_eq_zero_iff X la G.w wF _ x).2 hx

end PoleLengthBounds
