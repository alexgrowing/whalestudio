import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectivePairingFiniteFamily
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
theorem _root_.GlobalTheory.T.injective_pairing_finite_family : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 → ∃ (d : ℕ) (a : Fin d → HermE D r), Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.Sep.exists_separating | exact GlobalTheory.CompanionTheory.WSum.Sep.exists_separating | (intros; apply GlobalTheory.CompanionTheory.WSum.Sep.exists_separating <;> assumption)
