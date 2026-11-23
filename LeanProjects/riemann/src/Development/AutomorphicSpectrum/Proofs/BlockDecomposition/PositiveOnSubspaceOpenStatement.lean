import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_on_subspace_open : ∀ (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε Z S} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn <;> assumption)
