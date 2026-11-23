import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacter
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_multiple_path_trivial_character : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.WSum.Level.level | exact GlobalTheory.CompanionTheory.WSum.Level.level | (intros; apply GlobalTheory.CompanionTheory.WSum.Level.level <;> assumption)
