import Development.WeilBound.ThetaLifts.LeviDeterminants.EvAdel
import Development.WeilBound.ThetaLifts.LeviDeterminants.SchwartzDq
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds

theorem PositivityTheory.ThKF0.evCone : GlobalTheory.ThK.EvCone := PositivityTheory.ThKF0.evCone_of_adel PositivityTheory.Mix.adelic_estimates_holds

theorem PositivityTheory.ThKF0.evZero_of_adapted (h : PositivityTheory.ThKF0.AdaptedModelEvaluationAtZero) : GlobalTheory.ThK.EvZero :=
  PositivityTheory.ThKF0.evZero_of_adel PositivityTheory.Mix.adelic_estimates_holds PositivityTheory.ThKF0.schwartzDq h
