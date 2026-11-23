import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodularStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniquenessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHoldsStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AsmMultMain

namespace PositivityTheory.RgBcC

theorem wave_existence_speed_multiplicity : WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg := by
  have hL : LgFacts := GlobalTheory.T.length_function_facts_hold
  have hU : Unimod := GlobalTheory.T.general_linear_group_unimodular
  have hS : SobG := GlobalTheory.T.sobolev_inequality_on_group
  have hR : RCalc := GlobalTheory.T.right_derivative_calculus_holds
  have hKU : KerUniq := GlobalTheory.T.wave_kernel_uniqueness
  have hA : AlgEst := GlobalTheory.T.algebra_estimate_for_regularity
  have hsp : WaveSpeed := GlobalTheory.T.finite_propagation_speed_holds hL hU hR
  have hcpt : WaveCpt := Fc.asmCpt hL hU hR hS
  have hex : WaveEx := GlobalTheory.T.wave_solution_existence hL hR hsp hcpt
  have hk1 : KerOne := Fc.asmKerOne hL hU hR hS hA hsp
  exact ⟨hex, hsp, GlobalTheory.T.wave_kernel_existence hL hR hsp hex hKU hk1,
    GlobalTheory.CompanionTheory.WaveMult.asmMult_main hL hU hR hsp hex hKU hk1⟩

end PositivityTheory.RgBcC
