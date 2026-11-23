import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.GradedCoef

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem image_filtration_decreasing (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T : ℕ) : FiltOk G la T := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    unfold Fk
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)))
  · unfold Fk
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ,
      (toWK_surjective X la G.w wF _).range_eq, Submodule.span_univ]
  · unfold Fk
    rw [eq_bot_iff, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    exact (toWK_eq_zero_iff X la G.w wF _ x).2 hx

end PI.PoleLengthCount
