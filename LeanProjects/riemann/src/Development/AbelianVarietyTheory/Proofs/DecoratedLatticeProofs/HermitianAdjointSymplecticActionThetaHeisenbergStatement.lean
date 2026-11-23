import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ x y : WO S T, symplO T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T y) = -symplO S T x y) ∧ (∀ g h (x : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (actO S T g h x) = actO T S h g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x)) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) ↔ IsThetaFunO ψ S T f) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T w) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) (heisO ψ S T w f) := by
  first | exact @GlobalTheory.AdjointPair.adjoint_clauses | exact GlobalTheory.AdjointPair.adjoint_clauses | (intros; apply GlobalTheory.AdjointPair.adjoint_clauses <;> assumption)
