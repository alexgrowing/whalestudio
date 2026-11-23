import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SignInvolutionDiagonalIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sign_involution_diagonal_iff : ∀ (D : D7) (V : HSp D) (b : Module.Basis (Fin V.rank) D.host.E V.V), (∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ (τ : D.what₂.Tau) (s : Module.End D.host.E V.V), (IsSignInv V τ s ∧ ∀ i, s (b i) = b i ∨ s (b i) = -b i) ↔ ∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i := by
  first | exact @GlobalTheory.SignBasis.signInv_diag_iff | exact GlobalTheory.SignBasis.signInv_diag_iff | (intros; apply GlobalTheory.SignBasis.signInv_diag_iff <;> assumption)
