import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedBasisOrthogonal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_basis_orthogonal : ∀ (D : D7) (V : HSp D) (s : InvFam V) (P N : Submodule D.host.E V.V) (τ₀ : D.what₂.Tau), IsOrthDec V τ₀ P N → (∀ τ, (∀ x ∈ P, s τ x = x) ∧ ∀ x ∈ N, s τ x = -x) → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Adapted V b s := by
  first | exact @GlobalTheory.FockCompare.exists_adapted_of_isOrthDec | exact GlobalTheory.FockCompare.exists_adapted_of_isOrthDec | (intros; apply GlobalTheory.FockCompare.exists_adapted_of_isOrthDec <;> assumption)
