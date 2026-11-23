import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positivity_pulls_back_to_subspace : ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (y.conjTranspose * G * y) S → ∃ T : Submodule ℂ (Fin m → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram <;> assumption)
