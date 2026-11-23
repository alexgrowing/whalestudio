import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_conjAdjointPullback_bijection : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (A : Fr S) (B : Fr T), ∃ j : PolF D T.rank S.rank ≃+ PolF D S.rank T.rank, (∀ (c : ℂ) P, j (c • P) = starRingEnd ℂ c • j P) ∧ ∀ f, IsVacF ψ θ A B f → IsVacF ψ θ B A (dag S T f) ∧ ∀ P, ptF ψ θ B A (dag S T f) (j P) = dag S T (ptF ψ θ A B f P) := by
  first | exact @GlobalTheory.FockAdjoint.fock_dag | exact GlobalTheory.FockAdjoint.fock_dag | (intros; apply GlobalTheory.FockAdjoint.fock_dag <;> assumption)
