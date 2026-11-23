import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_frameChange_same_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  first | exact @GlobalTheory.FrameChange.ptF_frame_change | exact GlobalTheory.FrameChange.ptF_frame_change | (intros; apply GlobalTheory.FrameChange.ptF_frame_change <;> assumption)
