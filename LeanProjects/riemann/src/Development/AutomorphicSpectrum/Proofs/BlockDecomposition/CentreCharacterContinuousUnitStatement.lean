import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnit
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_continuous_unit : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | exact GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | (intros; apply GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz <;> assumption)
