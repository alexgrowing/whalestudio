import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.LimBdFpm
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq CompanionTheory.LimBd.Main

theorem limSteps_of (hI : PI.DSInfCharCap.DSInfCharCap) : LimSteps :=
  ⟨generating_function_polynomial, span_powers, CompanionTheory.CapEig.capelli_coefficient_smooth, CompanionTheory.CapEig.capelli_coefficient_continuity,
    CompanionTheory.CapEig.coefEig_of_infChar hI, phase_zero_alt, beta_at_infinity_zero⟩

end CompanionTheory.WaveGrid
