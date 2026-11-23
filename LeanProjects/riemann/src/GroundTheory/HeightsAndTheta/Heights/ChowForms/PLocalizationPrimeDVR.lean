import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem LocalizationPrimeDVR.proof : LocalizationPrimeDVR.Statement := by
  intro R _ _ _ _ q p _ hq hp
  set O := Localization.AtPrime p
  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O,
      congrArg (Ideal.map (algebraMap R O)) hp, Ideal.map_span, Set.image_singleton]
  have hprin : (maximalIdeal O).IsPrincipal := ⟨⟨algebraMap R O q, hmax⟩⟩
  have hPID : IsPrincipalIdealRing O :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain O).out 4 0).mp hprin
  have hq0 : algebraMap R O q ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap R O) :=
      IsLocalization.injective O (p.primeCompl_le_nonZeroDivisors)
    exact hq.ne_zero (hinj (by rw [h, map_zero]))
  have hne : maximalIdeal O ≠ ⊥ := by
    rw [hmax, Ne, Ideal.span_singleton_eq_bot]
    exact hq0
  exact { hPID with not_a_field' := hne }

end GroundTheory.Heights₂.Heights
