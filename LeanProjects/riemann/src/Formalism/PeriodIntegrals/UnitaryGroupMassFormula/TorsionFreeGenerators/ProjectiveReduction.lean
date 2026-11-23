import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.RankOneStep

namespace PI.FGTFG

theorem projective_reduction : ProjStep := by
  intro R M _ _ _ _ _ _
  have htor : Submodule.torsion R M = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, smul_eq_zero] at ha
    exact (Submodule.mem_bot R).mpr (ha.resolve_left (nonZeroDivisors.coe_ne_zero a))
  haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact Module.Flat.projective_of_finitePresentation

end PI.FGTFG
